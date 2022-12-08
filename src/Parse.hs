module Parse where

import Prelude(read)
import Relude hiding(some, many)
import Syntax.Core
import Text.Megaparsec hiding(parse, State)
import Text.Megaparsec qualified as MP
import Data.Sequence(Seq((:<|)), (|>))
import Text.Megaparsec.Char
import Text.Megaparsec.Error
import Data.Map qualified as M
import Data.Char
import Data.Maybe

type Parser = ParsecT Void Text (ReaderT (M.Map String Natural) (State (Int, M.Map String Int)))

ws = many (try (char '\n') <|> try (char '\r') <|> try (char '\t') <|> char ' ')

reportError = \case
  Right x -> x
  Left e -> error (toText (errorBundlePretty e))

parse :: String -> Text -> (Term, (Int, M.Map Text Int))
parse fn t =
  second
    (second (M.mapKeys toText))
    (flip runState (0, mempty) (flip runReaderT mempty (reportError <$> (runParserT term fn t))))

term :: Parser Term
term =
  try (do
    string "["; ws
    mv <- fst <$> get
    name <-
      try (do
        name <- some alphaNumChar; ws
        string ":"; ws
        pure name) <|>
      pure ("_" <> show mv)
    inTy <- term; ws
    string "]"; ws
    string "->"; ws
    outTy <- local (M.insert name 0 . fmap (+1)) term
    pure (Pi (toText name) inTy outTy)) <|>
  try (do
    string "{"; ws
    name <- some alphaNumChar; ws
    string "."; ws
    body <- local (M.insert name 0 . fmap (+1)) term; ws
    string "}"
    pure (Lam (toText name) body)) <|>
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
      (_, m) <- get
      case M.lookup (c:cs) m of
        Just mv -> pure (MVar (toText (c:cs)) mv)
        Nothing -> do
          (mv, _) <- get
          modify \(mv, mc) -> (mv + 1, mc)
          pure (MVar (toText (c:cs)) mv)
    else do
      ctx <- ask
      case M.lookup (c:cs) ctx of
        Just ix -> pure (BVar (toText (c:cs)) ix)
        Nothing -> error (show (c:cs, ctx)))

apps :: Term -> (Term, Seq Term)
apps = \case
  App lam arg ->
    let (lam', args) = apps lam
    in (lam', args |> arg)
  tm -> (tm, mempty)

prettyPrint :: Term -> Text
prettyPrint = \case
  Pi name inTy outTy ->
    "[" <> name <> " : " <> prettyPrint inTy <> "] -> " <> prettyPrint outTy
  Lam name body -> "{" <> name <> ". " <> prettyPrint body <> "}"
  (apps -> (lam, arg :<| args)) ->
    "(" <> prettyPrint lam <> " " <> foldl' (\acc arg -> acc <> " " <> prettyPrint arg) (prettyPrint arg) args <> ")"
  Univ -> "*"
  BVar name _ -> name
  MVar name _ -> name
