module Extra.Prelude

||| Zip, but it works on Streams
export
zip : Stream a -> List b -> List (a, b)
zip _ [] = []
zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys
