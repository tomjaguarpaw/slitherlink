import qualified Data.Map
import Data.List (tails, sortBy)
import Data.Maybe (fromJust, isNothing)
import Data.Ord (comparing)
import Text.Read (readMaybe)
import Data.Function (fix)

data EdgeDirection = South | East deriving (Ord, Eq, Show, Read)

data EdgePresence = Present | Absent deriving (Eq, Show)

data Arena a = Arena { arenaWidth   :: Int
                     , arenaHeight  :: Int
                     , arenaNumbers :: Data.Map.Map Face Int
                     , arenaEdges   :: Data.Map.Map Edge a
                     } deriving Show

type Face = (Int, Int)
type Vertex = (Int, Int)
type Edge = (Vertex, EdgeDirection)

data StepResult = Solved
                | Step (Arena (Maybe EdgePresence))
                | Unsolvable
                | Don'tKnowWhatToDo

setPresence :: Arena (Maybe edgePresence) -> Edge -> edgePresence -> Arena (Maybe edgePresence)
setPresence a e p = a { arenaEdges = Data.Map.insert e (Just p)  (arenaEdges a) }

refutable :: Int -> [Edge] -> Arena (Maybe EdgePresence) -> Bool
refutable 0 _  a = immediatelyRefutable a
refutable n es a =
    immediatelyRefutable a
    || or
         (flip map (tails es) $ \some_es ->
             case some_es of
               []           -> False
               (e:other_es) ->
                  if isNothing (edgeLabel a e)
                  then all (refutable (n-1) other_es)
                           [ setPresence a e Present
                           , setPresence a e Absent
                           ]
                  else False)

distance :: Edge -> Edge -> Int
distance ((x1, y1), _) ((x2, y2), _) = abs (x2 - x1) + abs (y2 - y1)

stepR :: Arena (Maybe EdgePresence) -> StepResult
stepR a = case undecidedEdges of
  []    -> Solved
  (_:_) -> case mNext of
             Nothing   -> Don'tKnowWhatToDo
             Just next -> Step next

  where undecidedEdges = filter (isNothing . edgeLabel a) (arenaEdgesT a)
        refutationAttempts0 =
          flip concatMap undecidedEdges (\e ->
            let nearby = sortBy (comparing (distance e)) $ filter (\e1 -> distance e e1 <= 2) undecidedEdges
            in let aP = setPresence a e Present
                   aA = setPresence a e Absent
               in
               -- Yes, these go the opposite way
               [ (refutable 0 nearby aP, aA)
               , (refutable 0 nearby aA, aP)
               ])
        refutationAttempts =
          flip concatMap undecidedEdges (\e ->
            let nearby = sortBy (comparing (distance e)) $ filter (\e1 -> distance e e1 <= 2) undecidedEdges
            in let aP = setPresence a e Present
                   aA = setPresence a e Absent
               in
               -- Yes, these go the opposite way
               [ (refutable 1 nearby aP, aA)
               , (refutable 1 nearby aA, aP)
               ])
        refutationAttempts2 =
          flip concatMap undecidedEdges (\e ->
            let nearby = sortBy (comparing (distance e)) $ filter (\e1 -> distance e e1 <= 2) undecidedEdges
            in let aP = setPresence a e Present
                   aA = setPresence a e Absent
               in
               -- Yes, these go the opposite way
               [ (refutable 2 nearby aP, aA)
               , (refutable 2 nearby aA, aP)
               ])
        refutationAttempts3 =
          flip concatMap undecidedEdges (\e ->
            let nearby = sortBy (comparing (distance e)) $ filter (\e1 -> distance e e1 <= 2) undecidedEdges
            in let aP = setPresence a e Present
                   aA = setPresence a e Absent
               in
               -- Yes, these go the opposite way
               [ (refutable 3 nearby aP, aA)
               , (refutable 3 nearby aA, aP)
               ])
        refutationAttemptsMany =
          flip concatMap undecidedEdges (\e ->
            let nearby = sortBy (comparing (distance e)) $ filter (\e1 -> distance e e1 <= 2) undecidedEdges
            in let aP = setPresence a e Present
                   aA = setPresence a e Absent
               in
               -- Yes, these go the opposite way
               [ (refutable 5 nearby aP, aA)
               , (refutable 5 nearby aA, aP)
               ])
        mNext = fmap snd (firstThat fst (refutationAttempts0 ++ refutationAttempts ++ refutationAttempts2 ++ refutationAttempts3 ++ refutationAttemptsMany))

firstThat :: (a -> Bool) -> [a] -> Maybe a
firstThat _ [] = Nothing
firstThat p (x:xs) = if p x then Just x else firstThat p xs


step :: Arena (Maybe EdgePresence) -> StepResult
step a = case undecidedEdges of
  []    -> Solved
  (_:_) -> go undecidedEdges

  where go []     = Don'tKnowWhatToDo
        go (x:xs) =
          let aWith    = a { arenaEdges = Data.Map.insert x (Just Present) (arenaEdges a) }
              aWithout = a { arenaEdges = Data.Map.insert x (Just Absent)  (arenaEdges a) }
          in case (validSoFar aWith, validSoFar aWithout) of
            (True, True)   -> go xs
            (False, False) -> Unsolvable
            (True, False)  -> Step aWith
            (False, True)  -> Step aWithout

        undecidedEdges = filter (isNothing . edgeLabel a) (arenaEdgesT a)

step2 :: Arena (Maybe EdgePresence) -> StepResult
step2 a = case undecidedEdgePairs of
  []    -> Solved
  (_:_) -> go undecidedEdgePairs

  where go []     = Don'tKnowWhatToDo
        go ((x1,x2):xs) =
          let aNeither = a { arenaEdges = Data.Map.insert x1 (Just Absent)
                                          $ Data.Map.insert x2 (Just Absent)
                                          $ (arenaEdges a) }
              aFirst   = a { arenaEdges = Data.Map.insert x1 (Just Present)
                                          $ Data.Map.insert x2 (Just Absent)
                                          $ (arenaEdges a) }
              aSecond  = a { arenaEdges = Data.Map.insert x1 (Just Absent)
                                          $ Data.Map.insert x2 (Just Present)
                                          $ (arenaEdges a) }
              aBoth    = a { arenaEdges = Data.Map.insert x1 (Just Present)
                                          $ Data.Map.insert x2 (Just Present)
                                          $ (arenaEdges a) }

          in case filter validSoFar [aNeither, aFirst, aSecond, aBoth] of
            []      -> Unsolvable
            [only]  -> Step only
            (_:_:_) -> go xs

        undecidedEdgePairs :: [(Edge, Edge)]
        undecidedEdgePairs = do
          vertex <- arenaVertices a
          let undecidedEdges = filter (isNothing . edgeLabel a) (edgesOfVertex a vertex)
          edge1  <- undecidedEdges
          edge2  <- undecidedEdges
          if edge1 /= edge2
          then return (edge1, edge2)
          else []

arenaEdgesT :: Arena a -> [Edge]
arenaEdgesT a = edgesHW (arenaWidth a) (arenaHeight a)

arenaFaces :: Arena a -> [Face]
arenaFaces arena = do
  x <- [1..arenaWidth arena]
  y <- [1..arenaHeight arena]
  return (x, y)

arenaVertices :: Arena a -> [Vertex]
arenaVertices arena = do
  x <- [0..arenaWidth arena]
  y <- [0..arenaHeight arena]
  return (x, y)

edgesOfFace :: Face -> [Edge]
edgesOfFace (x, y) = [ ((x-1, y-1), East)
                     , ((x-1, y-1), South)
                     , ((x-1, y), East)
                     , ((x, y-1), South)
                     ]

edgesOfVertex :: Arena a -> Vertex -> [Edge]
edgesOfVertex arena (x, y) = verticals ++ horizontals
  where verticals | x == 0 = [((x, y), East)]
                  | x == arenaWidth arena = [((x - 1, y), East)]
                  | otherwise = [((x, y), East), ((x - 1, y), East)]
        horizontals | y == 0 = [((x, y), South)]
                    | y == arenaHeight arena = [((x, y - 1), South)]
                    | otherwise = [((x, y), South), ((x, y - 1), South)]

faceNeighbours :: Arena a -> Face -> [(Face, Edge)]
faceNeighbours a (x, y) = horizontals ++ verticals
    where horizontals | x == 1 = [((x + 1, y), ((x, y -1), South))]
                      | x == arenaWidth a = [((x - 1, y), ((x - 1, y - 1), South))]
                      | otherwise = [((x + 1, y), ((x, y -1), South)), ((x - 1, y), ((x - 1, y - 1), South))]
          verticals | y == 1 = [((x, y + 1), ((x-1, y), East))]
                    | y == arenaHeight a = [((x, y-1), ((x - 1, y - 1), East))]
                    | otherwise = [((x, y + 1), ((x-1, y), East)), ((x, y-1), ((x - 1, y - 1), East))]

validFaceSoFar :: Arena (Maybe EdgePresence) -> Face -> Bool
validFaceSoFar arena face = case Data.Map.lookup face (arenaNumbers arena) of
  Nothing     -> True
  Just number -> (definitelyPresent <= number) && (number <= possiblyPresent)
    where edges   = edgesOfFace face
          edgePresences = map (edgeLabel arena) edges
          definitelyPresent = length (filter (== Just Present) edgePresences)
          notSure = length (filter (== Nothing) edgePresences)
          possiblyPresent = definitelyPresent + notSure

validVertexSoFar :: Arena (Maybe EdgePresence) -> Vertex -> Bool
validVertexSoFar arena vertex =
  ((definitelyPresent <= 0) && (0 <= possiblyPresent))
  || ((definitelyPresent <= 2) && (2 <= possiblyPresent))
  where edges = edgesOfVertex arena vertex
        edgePresences = map (edgeLabel arena) edges
        definitelyPresent = length (filter (== Just Present) edgePresences)
        notSure = length (filter (== Nothing) edgePresences)
        possiblyPresent = definitelyPresent + notSure


immediatelyRefutable :: Arena (Maybe EdgePresence) -> Bool
immediatelyRefutable = not . validSoFar

validSoFar :: Arena (Maybe EdgePresence) -> Bool
validSoFar arena = all (validFaceSoFar arena) (arenaFaces arena)
                   && all (validVertexSoFar arena) (arenaVertices arena)

edgeLabel :: Arena a -> Edge -> a
edgeLabel a = fromJust . flip Data.Map.lookup (arenaEdges a)

printArena :: Arena (Maybe EdgePresence) -> IO ()
printArena arena = do
  flip mapM_ (filter (/= (0, True)) ((,) <$> [0..arenaHeight arena] <*> [True, False])) $ \(y, yIsFace) -> do
    flip mapM_ (filter (/= (0, True)) ((,) <$> [0..arenaWidth arena] <*> [True, False])) $ \(x, xIsFace) -> do
      case (xIsFace, yIsFace) of
        (False, False) -> putStr "+"
        (False, True)  -> putStr (char (edgeLabel arena ((x, y-1), South)) South)
        (True, False)  -> putStr (char (edgeLabel arena ((x-1, y), East))  East)
        (True, True)   -> putStr (case (Data.Map.lookup (x, y) (arenaNumbers arena)) of
                                    Nothing -> " "
                                    Just n  -> show n)
    putStr "\n"

char :: Maybe EdgePresence -> EdgeDirection -> String
char Nothing _ = "."
char (Just Present) South = "|"
char (Just Present) East  = "-"
char (Just Absent)  South = " "
char (Just Absent)  East  = " "

data Choice = P Edge | A Edge deriving Read

main :: IO ()
main = do
  loop (arenaOfFoo hardPuzzle) 0

  where loop a n = do
          print n
          printArena a
          case stepR a of
            Step a' -> loop a' (n + 1)
            Don'tKnowWhatToDo -> do
                putStrLn "Didn't do anything"

                fix (\continue -> do
                    line <- getLine
                    case readMaybe line of
                      Just (A e) -> loop (setPresence a e Absent) n
                      Just (P e) -> loop (setPresence a e Present) n
                      Nothing    -> continue)

            Unsolvable -> putStrLn "Unsolvable"
            Solved -> putStrLn "Solved"

emptyArena :: Int -> Int -> Arena (Maybe EdgePresence)
emptyArena x y = Arena x y Data.Map.empty (Data.Map.fromList edges')
  where edges' = map (\x -> (x, Nothing)) (edgesHW x y)

edgesHW :: Int -> Int -> [Edge]
edgesHW x y = edges
  where edges = do
          xi <- [0..x]
          yi <- [0..y]
          if (xi < x) && (yi < y)
          then [((xi,yi), South), ((xi, yi), East)]
          else if (xi < x)
          then [((xi,yi), East)]
          else if (yi < y)
          then [((xi,yi), South)]
          else []

data Foo = Foo { unFoo :: Maybe Int }

instance Num Foo where
  fromInteger = Foo . Just . fromInteger
  (+) = undefined
  (*) = undefined
  abs = undefined
  signum = undefined
  negate = undefined

__ :: Foo
__ = Foo Nothing

pid21153 :: [[Foo]]
pid21153 =
  [ [  3,  3,  3,  2,  0,  1,  3,  2,  3,  3]
  , [ __, __,  0, __,  1,  1, __,  1, __, __]
  , [  2, __,  1, __, __, __, __,  2, __,  3]
  , [  2,  2, __, __,  2,  1, __, __,  2,  1]
  , [  3,  2, __,  2, __, __,  1, __,  3,  1]
  , [  2,  2, __,  2, __, __,  2, __,  2,  1]
  , [  1,  2, __, __,  2,  1, __, __,  1,  3]
  , [  3, __,  2, __, __, __, __,  3, __,  3]
  , [ __, __,  2, __,  1,  0, __,  1, __, __]
  , [  3,  2,  1,  1,  1,  2,  3,  3,  3,  3]
  ]

puzzle :: [[Foo]]
puzzle = [ [__, __,  3,  3, __]
         , [ 2, __,  0,  2,  1]
         , [__, __,  2, __,  2]
         , [__, __, __, __,  2]
         , [ 3,  1,  2,  2,  3]
         ]

hardPuzzle :: [[Foo]]
hardPuzzle =
  [ [  3,  2,  2,  2, __, __,  2, __, __,  2]
  , [ __, __,  2,  1,  3, __,  3, __, __,  3]
  , [ __, __, __, __,  1, __, __, __,  2,  1]
  , [  1,  3, __,  2,  1, __,  2, __,  3,  1]
  , [ __, __, __, __,  2,  2,  2,  1,  1, __]
  , [ __,  3,  3,  3,  2,  3, __, __, __, __]
  , [  2,  2, __,  2, __,  1,  0, __,  2,  1]
  , [  2,  3, __, __, __,  1, __, __, __, __]
  , [  3, __, __,  2, __,  0,  1,  2, __, __]
  , [  2, __, __,  2, __, __,  3,  3,  2,  3]
  ]

harderPuzzle :: [[Foo]]
harderPuzzle =
  [ [ __, __,  2,  2,  2, __, __,  2,  3, __ ]
  , [  2,  3, __,  2, __, __, __,  2,  1, __ ]
  , [  2,  3, __,  1,  2,  2,  2, __, __,  2 ]
  , [ __, __,  2, __,  3, __, __,  2,  3,  2 ]
  , [ __, __,  2, __, __, __,  2,  0, __,  2 ]
  , [  3, __,  1,  2, __, __, __,  1, __, __ ]
  , [  1,  1,  0, __, __,  1, __,  3, __, __ ]
  , [  1, __, __,  1,  3,  1,  1, __,  3,  3 ]
  , [ __,  1,  1, __, __, __,  3, __,  2,  1 ]
  , [ __,  1,  2, __, __,  2,  2,  3, __, __ ]
  ]

harderPuzzlePartial =
  foldl (\a (e, p) -> setPresence a e p) (arenaOfFoo harderPuzzle)
  [ (((9, 4), South), Absent)
  , (((8, 0), East), Present)
  , (((9, 0), South), Present)
  , (((3,0), East), Present)
  , (((2,0), East), Present)
  , (((1,1), East), Present)
  , (((1,1), South), Present)
  , (((1,2), East), Present)
  , (((7,6), East), Present)
  , (((7,6), South), Present)
  , (((8,7), East), Absent)
  , (((3,2), East), Absent)
  , (((4,2), South), Absent)
  , (((0,7), East), Absent)
  , (((6,8), East), Present)
  , (((6,8), South), Present)
  , (((8,9), South), Present)
  , (((7,10), East), Present)
  , (((9,5), East), Absent)
  , (((0,5), South), Present)
  , (((2,5), South), Present)
  , (((0,4), South), Present)
  , (((2,8), East), Present)
  ]

pid21153partial =
  foldl (\a (e, p) -> setPresence a e p) (arenaOfFoo pid21153)
  [ (((9, 0), South), Present)
  , (((3, 6), South), Absent)
  , (((6, 7), East),  Absent)
  ]


arenaOfFoo :: [[Foo]] -> Arena (Maybe EdgePresence)
arenaOfFoo foo = empty { arenaNumbers = ns }
  where h = length foo
        w = length (foo !! 0)
        empty = emptyArena h w
        ns = Data.Map.fromList $ do
          (y, row)  <- zip [1..] foo
          (x, foon) <- zip [1..] row
          case unFoo foon of
            Nothing -> []
            Just n  -> return ((x, y), n)
