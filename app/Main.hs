module Main (main) where

import Control.Applicative
import Data.Fix
import Data.Functor
import Data.Functor.Classes
import Data.Functor.Compose
import Data.Text (Text)
import Data.Void
import Generic.Data
import Text.Megaparsec
import Text.Megaparsec.Char.Lexer (decimal)

-- Here's what all our work will enable:
main :: IO ()
main = do
  let input = "3 * 3 + 4 + (2 * 3 + 1) * 5 * 6 + 20"
  -- Parse the String into an Expr that can be run. Parsing either fails (in
  -- which case we print a helpful error message) or it succeeds and we return
  -- the value.
  rawExpr <- either (fail . errorBundlePretty) return $ parseExpr input
  -- The rawExpr is right associative and doesn't understand operator
  -- precedence. We need to fix that before going farther.
  let expr = fixPrecedence $ fixAssociativity rawExpr
  -- Now we can interpret our language in various ways. These three lines will
  -- print:
  -- ((((3 * 3) + 4) + ((((2 * 3) + 1) * 5) * 6)) + 20)
  -- 9
  -- 243
  putStrLn $ toString expr
  print $ countNumbers expr
  print $ calculate expr

-- # Definitions

-- | First we'll define the language we're trying to parse. It's just basic
-- arithmetic, but the generic argument might look weird. Anywhere we'd normally
-- use recursion, we use the generic argument. This has a bunch of benefits as
-- we'll see later on. We'll also ask the compiler to derive a bunch of things
-- for us. "Functor", "Foldable", and "Traversable" allow us to iterate over the
-- recursive parts of our data structure.
data ExprF f = Operand (Operand f) | BinOp Operator f f
  deriving (Functor, Foldable, Traversable, Show, Generic1)
  deriving (Show1) via Generically1 ExprF

data Operator = Add | Mul
  deriving (Show)

data Operand f = Number Int | Paren f
  deriving (Functor, Foldable, Traversable, Show, Generic1)
  deriving (Show1) via Generically1 Operand

-- | Fix is a recursive datatype defined in a library. `Fix f` is equivalent to
-- `f (f (f (f ...)))` if you could write out an infinite number of fs. That
-- means Expr is ExprF applied to itself as many times as needed.
type Expr = Fix ExprF

-- #
-- # Interpreting
-- #

-- | Interpreting the language is extremely simple! We use the `foldFix`
-- function to tear our Expr down into a single number. We define how to handle
-- a single step assuming the child steps already ran, and `foldFix` takes care
-- of the recursion. Fun fact about Haskell: although it seems like you should
-- have to compute all the children before you can compute the parent, this is
-- lazy so children will only be computed when the parent needs their value. For
-- example, if we decided that all Paren expressions should just evaluate to `4`
-- instead of actually running the inner expressions, Haskell would never
-- compute the values in parentheses.
calculate :: Expr -> Int
calculate = foldFix \case
  Operand (Number n) -> n
  Operand (Paren n) -> n
  BinOp Add a b -> a + b
  BinOp Mul a b -> a * b

-- | Another way of interpretting an Expression is to count how many numbers
-- there are.
countNumbers :: Expr -> Int
countNumbers = foldFix \case
  Operand (Number _) -> 1
  -- We can flatten all the other cases into this one because ExprF implements
  -- Foldable.
  expr -> sum expr

-- | And finally this way of interpretting an Expression just prints it with
-- explicit parhentheses.
toString :: Expr -> String
toString = foldFix \case
  BinOp op l r -> "(" ++ l ++ opToString op ++ r ++ ")"
  Operand (Number n) -> show n
  -- Ironically we don't need parentheses here because the child expression will
  -- already have them if they're needed.
  Operand (Paren n) -> n
 where
  opToString Add = " + "
  opToString Mul = " * "

-- # Parsing
--
-- Parsing is a bit strange. The basic idea is that we'll generate all possible
-- parse trees, then prune them until only one remains.

-- | This is the parse tree we'll be working with. It's right associative
-- because parsing is hard. To get something really nice and natually left
-- recursive I think I'd need to either switch parsing libraries or create an
-- even stranger looking type. Anyway, we can get around the associativity
-- problems with post-processing.
data ExprParse f = OpParse (OperandP f) f
  deriving (Functor, Foldable, Traversable)

data OperandP f = ParenP f | NumberP
  deriving (Functor, Foldable, Traversable)

-- | This is pretty much the same as ExprF but the type enforces that it's right
-- associative. This'll be easier to work with when doing the initial parsing.
data ExprRightF f = OperandR (Operand f) | BinOpR Operator (Operand f) f
  deriving (Functor, Foldable, Traversable, Show, Generic1)
  deriving (Show1) via Generically1 ExprRightF

type ExprRight = Fix ExprRightF

-- | This tells you how to grow all the parse trees. Anytime you see `()` in a
-- value in the parser, you can read it as a seed. The tree will continue
-- growing from that point.
type ParserGrower e = [e ()]

-- | Defines how to grow all the parse trees for our Expr language. We place
-- seeds in the rhs of the operation (because it's right associative) and in any
-- parentheses.
exprParseGrower :: ParserGrower ExprParse
exprParseGrower = [lhs `OpParse` () | lhs <- [NumberP, ParenP ()]]

-- | This tells you how to prune away a parse tree.
type ParserPruner e = e (Parser ExprRight) -> Parser ExprRight

-- | A pruner for Expressions.
exprPruner :: ParserPruner ExprParse
-- Anywhere you see `Fix` you can pretty much just ignore it. We just have to
-- wrap our expressions in it to appease the type system.
exprPruner (OpParse operandType rhsP) = fmap Fix do
  lhs <- parseOperand operandType
  parseOpAndRhs lhs <|> return (OperandR lhs)
 where
  parseOperand :: OperandP (Parser ExprRight) -> Parser (Operand ExprRight)
  parseOperand NumberP = Number <$> decimal
  parseOperand (ParenP expr) = fmap Paren $ "(" *> expr <* ")"

  parseOpAndRhs :: Operand ExprRight -> Parser (ExprRightF ExprRight)
  parseOpAndRhs lhs = do
    op <- " + " $> Add <|> " * " $> Mul
    BinOpR op lhs <$> rhsP

-- | Parses an Expression using everything defined so far
parseExpr :: Text -> Either _ ExprRight
-- refold allows us to build up and tear down a structure. It combines `foldFix`
-- with its opposite: `unfoldFix`. One really cool thing about refold is that it
-- "fuses" the building and tearing together so that you never actually
-- construct the whole intermediate data structure in memory.
parseExpr = parse (refold pruneTrees growTrees () <* eof) ""
 where
  pruneTrees (Compose xs) = asum $ fmap exprPruner xs
  growTrees = const $ Compose exprParseGrower

-- | After parsing, operators are all considered to have the same precedence.
-- Instead of trying to handle precedence in the parser, we post process it.
-- Technically this is another way of interpreting the original Expr, so we use
-- foldFix.
fixPrecedence :: Expr -> Expr
fixPrecedence = foldFix \case
  BinOp Mul (Fix (BinOp Add lhs innerRhs)) rhs -> Fix $ BinOp Add lhs (Fix $ BinOp Mul innerRhs rhs)
  expr -> Fix expr

-- | This is an Expr that's missing its operand
type ExprBuilder = (Operand Expr -> Expr)

-- | Given a right associative expression (the thing we got out of parsing)
-- reassociate all the operators to the left.
fixAssociativity :: ExprRight -> Expr
-- We're using foldFix in a way we haven't done before. When you tear down a
-- structure, you can return whatever type you want. Because any type is
-- allowed, functions are valid. Normally foldFix passes information bottom up,
-- but by returning a function we have a way of passing data top down as well.
fixAssociativity expr = foldFix smuggleUp expr (Fix . Operand)
 where
  -- Here's where using foldFix with a function return type comes into play.
  -- Each node is transformed into a function that can finish building an Expr
  -- by applying its operand to the Builder that will be passed to it. The name
  -- is a refernce to how you're taking nodes and passing them around to other
  -- parts of the tree.
  smuggleUp :: ExprRightF (ExprBuilder -> Expr) -> ExprBuilder -> Expr
  smuggleUp (BinOpR op operand rhsF) build =
    rhsF \b -> Fix $ BinOp op (build $ fixOperand operand) (Fix $ Operand b)
  smuggleUp (OperandR operand) build = build $ fixOperand operand

  fixOperand :: Operand (ExprBuilder -> f) -> Operand f
  fixOperand (Paren inner) = Paren $ inner $ Fix . Operand
  fixOperand (Number n) = Number n

-- | An alias for a Parser of Text with no special error state
type Parser = Parsec Void Text
