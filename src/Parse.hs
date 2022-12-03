module Parse where

import Prelude(read)
import Relude hiding(some, many)
import Syntax.Core
import Text.Megaparsec hiding(parse, State)
import Text.Megaparsec qualified as MP
import Text.Megaparsec.Char
import Data.Map qualified as M

type Parser = ParsecT Void Text (State (Int, M.Map String Int))

ws = many (try (char '\n') <|> try (char '\r') <|> try (char '\t') <|> char ' ')

parse :: String -> Text -> (Term, Int)
parse fn t = second fst (flip runState (0, mempty) (fromRight undefined <$> (runParserT term fn t)))

term :: Parser Term
term =
  try (do
    ix <- some digitChar
    pure (BVar (read ix))) <|>
  try (do
    string "["; ws
    inTy <- term; ws
    string "->"; ws
    outTy <- term; ws
    string "]"
    pure (Pi inTy outTy)) <|>
  -- try (do
  --   string "["
  --   inTys <- some do
  --     ws
  --     inTy <- term; ws
  --     string "->"
  --     pure inTy
  --   ws
  --   outTy <- term; ws
  --   string "]"
  --   pure (foldr Pi outTy inTys)) <|>
  try (do
    string "{"; ws
    body <- term; ws
    string "}"
    pure (Lam body)) <|>
  try (do
    string "("; ws
    lam <- term
    args <- some (ws *> term); ws
    string ")"
    pure (foldl' (\acc arg -> App acc arg) lam args)) <|>
  try (do
    string "U"
    pure Univ) <|>
  (do
    c <- alphaNumChar
    cs <- many (try alphaNumChar <|> digitChar)
    m <- snd <$> get
    case M.lookup (c:cs) m of
      Just mv -> pure (MVar mv)
      Nothing -> do
        mv <- fst <$> get
        modify (first (+1))
        pure (MVar mv))
