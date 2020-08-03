module Extra.Prelude

||| Copied from Prelude.Show, since it's not public
export
showParens : (1 b : Bool) -> String -> String
showParens False s = s
showParens True  s = "(" ++ s ++ ")"

||| Zip, but it works on Streams
export
zip : Stream a -> List b -> List (a, b)
zip _ [] = []
zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys
