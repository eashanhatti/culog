module Parse where

import Prelude(read)
import Relude hiding(some, many)
import Syntax.Core
import Text.Megaparsec hiding(parse, State)
import Text.Megaparsec qualified as MP
import Text.Megaparsec.Char
import Text.Megaparsec.Error
import Data.Map qualified as M
import Data.Char
import Data.Maybe

type Parser = ParsecT Void Text (State (Int, M.Map String Natural, M.Map String Int))

ws = many (try (char '\n') <|> try (char '\r') <|> try (char '\t') <|> char ' ')

reportError = \case
  Right x -> x
  Left e -> error (toText (errorBundlePretty e))

parse :: String -> Text -> (Term, Int)
parse fn t =
  let (tm, (mv, _, _)) = flip runState (0, mempty, mempty) (reportError <$> (runParserT term fn t))
  in (tm, mv)

term :: Parser Term
term =
  try (do
    string "["; ws
    name <-
      try (do
        name <- some alphaNumChar; ws
        string ":"; ws
        pure name) <|>
      pure "_"
    inTy <- term; ws
    string "]"; ws
    string "->"; ws
    modify \(mv, ctx, mc) -> (mv, M.insert name 0 (fmap (+1) ctx), mc)
    outTy <- term
    modify \(mv, ctx, mc) -> (mv, M.delete name (fmap (subtract 1) ctx), mc)
    pure (Pi inTy outTy)) <|>
  try (do
    string "{"; ws
    name <- some alphaNumChar; ws
    string "."; ws
    modify \(mv, ctx, mc) -> (mv, M.insert name 0 (fmap (+1) ctx), mc)
    body <- term; ws
    modify \(mv, ctx, mc) -> (mv, M.delete name (fmap (subtract 1) ctx), mc)
    string "}"
    pure (Lam body)) <|>
  try (do
    string "("; ws
    lam <- term
    args <- some (ws *> term); ws
    string ")"
    pure (foldl' (\acc arg -> App acc arg) lam args)) <|>
  try (do
    string "*"
    pure Univ) <|>
  (do
    c <- alphaNumChar
    cs <- many (try alphaNumChar <|> digitChar)
    if isUpper c then do
      (_, _, m) <- get
      case M.lookup (c:cs) m of
        Just mv -> pure (MVar mv)
        Nothing -> do
          (mv, _, _) <- get
          modify \(mv, ctx, mc) -> (mv + 1, ctx, mc)
          pure (MVar mv)
    else do
      (_, ctx, _) <- get
      case M.lookup (c:cs) ctx of
        Just ix -> pure (BVar ix)
        Nothing -> error (show (c:cs, ctx)))

