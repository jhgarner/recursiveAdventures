{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Main (main) where

import Control.Applicative
import Control.Monad.Free
import Data.Fix (Fix (..))
import Data.Functor
import Data.Functor.Classes
import Data.Functor.Compose
import Data.Functor.Foldable
import Data.Functor.Identity
import Data.Text (Text)
import Data.Void
import GHC.Exts (IsList (..))
import Generic.Data
import Text.Megaparsec
import Text.Megaparsec.Char.Lexer (decimal)

main :: IO ()
main = do
  -- You'd probably generate this expression parsing or something
  -- let Right expr = parseOnly (exprParser <* endOfInput) "1 + (5 - 3) + 2 + 4"
  -- print expr
  let input = "3 * 3 + 4 + (2 * 3 + 1) * 5 * 6 + 20"
  -- let input = "3 * 3 + 4 + 8 * 5 * 6 + 20"
  rawExpr <- either (fail . errorBundlePretty) pure $ parseExpr input
  let expr = fixPrecedence $ fixAssociativity rawExpr
  -- print $ printExpr rawExpr
  print $ printExpr expr
  print $ countNumbers expr
  print $ interpret expr

-- | First we'll define the language we're trying to parse. It's just basic
-- arithmetic, but the generic argument might look weird. Anywhere we'd normally
-- use recursion, we use the generic argument. This has a bunch of benefits as
-- we'll see later on. We'll also ask the compiler to derive a bunch of things
-- for us. Things like "Functor" and "Foldable" only make sense because our type
-- has a generic type.
data ExprF f = Operand (Operand f) | BinOp Operator f f
  deriving (Functor, Foldable, Traversable, Show, Generic1)
  deriving (Show1) via Generically1 ExprF

data Operator = Add | Mul
  deriving (Show)

data Operand f = Number Int | Paren f
  deriving (Functor, Foldable, Traversable, Show, Generic1)
  deriving (Show1) via Generically1 Operand

-- | Fix is a recursive datatype defined in a library. `Fix f` is equivalent to
-- `f (f (f (f ...)))` if you could write out an infinite number of fs.
type Expr = Fix ExprF

-- | Interpreting the language is extremely simple! We use the unhelfully named
-- `cata` function to tear our Expr down into a single number. We define how to
-- handle a single step assuming the child steps already ran, and `cata` takes
-- care of the recursion. Fun fact about Haskell: although it seems like you
-- should have to compute all the children before you can compute the parent,
-- this is lazy so children will only be computed when the parent uses their
-- value. For example, if we decided that all Paren expressions should just
-- evaluate to `4` instead of actually running the inner expressions, Haskell
-- would never compute them.
interpret :: Expr -> Int
interpret = cata \case
  Operand (Number n) -> n
  Operand (Paren n) -> n
  BinOp Add a b -> a + b
  BinOp Mul a b -> a * b

-- | Another way of interpretting an Expression is to count how many numbers
-- there are.
countNumbers :: Expr -> Int
countNumbers = cata \case
  Operand (Number _) -> 1
  -- We can flatten all the other cases into this one because ExprF implements
  -- Foldable.
  expr -> sum expr

-- | And finally this way of interpretting an Expression just prints it with
-- explicit associativity.
printExpr :: Expr -> String
printExpr = cata \case
  BinOp Add l r -> "(" ++ l ++ " + " ++ r ++ ")"
  BinOp Mul l r -> "(" ++ l ++ " * " ++ r ++ ")"
  Operand (Number n) -> show n
  -- Ironically we don't need parentheses here because the child expression will
  -- already have them if they're needed.
  Operand (Paren n) -> n

-- # Parsing
--
-- Parsing is a bit strange. The basic idea is that we'll generate all possible
-- parse trees, then prune them until only one remains.

-- | This is the parse tree we'll be working with. It's right associative
-- because parsing is hard. To get something really nice and natually left
-- recursive I think I'd need to either switch parsing library or create an even
-- stranger looking type.
data ExprFlat f = OpFlat (OperandP f) f
  deriving (Functor, Foldable, Traversable)

data OperandP f = ParenP f | NumberP
  deriving (Functor, Foldable, Traversable)

data ExprRightF f = OperandR (Operand f) | BinOpR Operator (Operand f) f
  deriving (Functor, Foldable, Traversable, Show, Generic1)
  deriving (Show1) via Generically1 ExprRightF

type ExprRight = Fix ExprRightF

-- | Many creates trees of es.
-- Compose takes two Functors and creates a new Functor combining the two.
-- Compose [] e a = [e a]
type Many e = Compose [] e

-- | This tells you how to grow all the parse trees.
type ParserGrower e = [e (Free (Many e) ())]

-- | Anytime you see a seed in a ParserGrower, it means that a new arbitrary
-- tree can grow from that point.
seed :: Functor f => Free f ()
seed = Pure ()

-- | Defines how to grow all the parse trees for our Expr language. We're not
-- actually using the full power of `seed` and `Free` here, but an earlier
-- version needed it so I've kept it around. Basically `Free` gives us more
-- control over what subtrees can expand into.
allExprFlats :: ParserGrower ExprFlat
allExprFlats = [lhs `OpFlat` seed | lhs <- [NumberP, ParenP seed]]

-- | This tells you how to prune away a parse tree
type ParserPruner e = e (Parser ExprRight) -> Parser ExprRight

-- | Defines how to prune a parse tree into an Expression.
flatParser :: ParserPruner ExprFlat
-- Anywhere you see `Fix` you can pretty much just ignore it. We just have to
-- wrap our expressions in it to appease the type system.
flatParser (OpFlat operandType rhsP) = fmap Fix do
  lhs <- parseOperand operandType
  parseOpAndRhs lhs <|> pure (OperandR lhs)
 where
  parseOperand :: OperandP (Parser ExprRight) -> Parser (Operand ExprRight)
  parseOperand NumberP = Number <$> decimal
  parseOperand (ParenP expr) = fmap Paren $ "(" *> expr <* ")"

  parseOpAndRhs :: Operand ExprRight -> Parser (ExprRightF ExprRight)
  parseOpAndRhs lhs = do
    op <- " + " $> Add <|> " * " $> Mul
    BinOpR op lhs <$> rhsP

-- | Creates a parser that finds the correct parse tree
pruneTrees :: ParserPruner e -> Many e (Parser ExprRight) -> Parser ExprRight
pruneTrees parser (Compose xs) = asum $ fmap parser xs

-- | Parses an Expression using everything defined so far
parseExpr :: Text -> Either _ ExprRight
-- Yes cataFutu is an obtuse name, but it matches the "literature". Basically
-- cataFutu means that we'll build up our data structure using `futu` and tear
-- it down using `cata`. `cata` you've already seen. `futu` works with Free to
-- give us a lot of control over how we build our data structure.
parseExpr = parse (cataFutu (pruneTrees flatParser) (const $ fromList allExprFlats) () <* eof) ""

-- | After parsing, operators are all considered to have the same precedence.
-- Instead of trying to handle precedence in the parser, we post process it.
-- Technically this is another way of interpreting the original Expr, so we use
-- cata.
fixPrecedence :: Expr -> Expr
fixPrecedence = cata \case
  BinOp Mul (Fix (BinOp Add lhs innerRhs)) rhs -> Fix $ BinOp Add lhs (Fix $ BinOp Mul innerRhs rhs)
  expr -> Fix expr

-- | This is an Expr that's missing its operand
type ExprBuilder = (Operand Expr -> Expr)

-- | Given a right associative expression (the thing we got out of parsing)
-- reassociate all the operators to the left.
fixAssociativity :: ExprRight -> Expr
-- We're using cata in a way we haven't done before. When you tear down a
-- structure, you can return whatever type you want. Because any type is
-- allowed, functions are valid. Normally cata passes information bottom up, but
-- by returning a function we have a way of passing data top down as well.
fixAssociativity expr = cata smuggleUp expr (Fix . Operand)
 where
  -- Here's where using cata with a function return type comes into play. Each
  -- node is transformed into a function that can finish building an Expr by
  -- applying its operand to the Builder that will be passed to it. The name is
  -- a refernce to how you're taking nodes and passing them around to other
  -- parts of the tree.
  smuggleUp :: ExprRightF (ExprBuilder -> Expr) -> ExprBuilder -> Expr
  smuggleUp (BinOpR op operand rhsF) build =
    rhsF $ \b -> Fix $ BinOp op (build $ fixOperand operand) (Fix $ Operand b)
  smuggleUp (OperandR operand) build = build $ fixOperand operand

  fixOperand :: Operand ((Operand Expr -> Expr) -> f) -> Operand f
  fixOperand (Paren inner) = Paren $ inner $ Fix . Operand
  fixOperand (Number n) = Number n

-- #
-- # Everything below this point would be defined in a generic library
-- #

type Parser = Parsec Void Text

cataFutu :: Functor f => (f b -> b) -> (a -> f (Free f a)) -> a -> b
cataFutu alg coalg = ghylo distCata distFutu (alg . fmap runIdentity) coalg

instance IsList (Compose [] f a) where
  type Item (Compose [] f a) = f a
  fromList = Compose
  toList (Compose ls) = ls

instance IsList (f (Free f a)) => IsList (Free f a) where
  type Item (Free f a) = Item (f (Free f a))
  fromList ls = Free $ fromList ls
  toList (Free ls) = toList ls
  toList (Pure _) = []
