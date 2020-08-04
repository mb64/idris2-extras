||| Dependent sorted maps
|||
||| Mostly copied from Data.SortedMap, but with some changes
module Extra.Data.DepMap

import Decidable.Equality

||| Used to report errors when key lookups don't agree
public export
data BadKey : (k : Type) -> (Ord k, DecEq k) => Type where
  KeyIsBad : (Ord k, DecEq k)
    => (x : k) -> (y : k)
    -> (compare x y = EQ)
    -> Not (x = y)
    -> BadKey k

-- Multiplicities are very intentional here, I just haven't gotten around to
-- "linear"-izing the rest of the library
data Tree : Nat -> (k : Type) -> (k -> Type) -> Type where
  Leaf : (x : k) -> (1 _ : p x) -> Tree Z k p
  Branch2 :
    (1 _ : Tree n k p) -> k ->
    (1 _ : Tree n k p) ->
    Tree (S n) k p
  Branch3 :
    (1 _ : Tree n k p) -> k ->
    (1 _ : Tree n k p) -> k ->
    (1 _ : Tree n k p) ->
    Tree (S n) k p

branch4 :
  (1 _ : Tree n k p) -> k ->
  (1 _ : Tree n k p) -> k ->
  (1 _ : Tree n k p) -> k ->
  (1 _ : Tree n k p) ->
  Tree (S (S n)) k p
branch4 a b c d e f g =
  Branch2 (Branch2 a b c) d (Branch2 e f g)

branch5 :
  (1 _ : Tree n k p) -> k ->
  (1 _ : Tree n k p) -> k ->
  (1 _ : Tree n k p) -> k ->
  (1 _ : Tree n k p) -> k ->
  (1 _ : Tree n k p) ->
  Tree (S (S n)) k p
branch5 a b c d e f g h i =
  Branch2 (Branch2 a b c) d (Branch3 e f g h i)

branch6 :
  (1 _ : Tree n k p) -> k ->
  (1 _ : Tree n k p) -> k ->
  (1 _ : Tree n k p) -> k ->
  (1 _ : Tree n k p) -> k ->
  (1 _ : Tree n k p) -> k ->
  (1 _ : Tree n k p) ->
  Tree (S (S n)) k p
branch6 a b c d e f g h i j k =
  Branch3 (Branch2 a b c) d (Branch2 e f g) h (Branch2 i j k)

branch7 :
  (1 _ : Tree n k p) -> k ->
  (1 _ : Tree n k p) -> k ->
  (1 _ : Tree n k p) -> k ->
  (1 _ : Tree n k p) -> k ->
  (1 _ : Tree n k p) -> k ->
  (1 _ : Tree n k p) -> k ->
  (1 _ : Tree n k p) ->
  Tree (S (S n)) k p
branch7 a b c d e f g h i j k l m =
  Branch3 (Branch3 a b c d e) f (Branch2 g h i) j (Branch2 k l m)

merge1 :
  (1 _ : Tree    n  k p) -> k ->
  (1 _ : Tree (S n) k p) -> k ->
  (1 _ : Tree (S n) k p) ->
  Tree (S (S n)) k p
merge1 a b (Branch2 c d e) f (Branch2 g h i) = branch5 a b c d e f g h i
merge1 a b (Branch2 c d e) f (Branch3 g h i j k) = branch6 a b c d e f g h i j k
merge1 a b (Branch3 c d e f g) h (Branch2 i j k) = branch6 a b c d e f g h i j k
merge1 a b (Branch3 c d e f g) h (Branch3 i j k l m) = branch7 a b c d e f g h i j k l m

merge2 :
  (1 _ : Tree (S n) k p) -> k ->
  (1 _ : Tree    n  k p) -> k ->
  (1 _ : Tree (S n) k p) ->
  Tree (S (S n)) k p
merge2 (Branch2 a b c) d e f (Branch2 g h i) = branch5 a b c d e f g h i
merge2 (Branch2 a b c) d e f (Branch3 g h i j k) = branch6 a b c d e f g h i j k
merge2 (Branch3 a b c d e) f g h (Branch2 i j k) = branch6 a b c d e f g h i j k
merge2 (Branch3 a b c d e) f g h (Branch3 i j k l m) = branch7 a b c d e f g h i j k l m

merge3 :
  (1 _ : Tree (S n) k p) -> k ->
  (1 _ : Tree (S n) k p) -> k ->
  (1 _ : Tree    n  k p) ->
  Tree (S (S n)) k p
merge3 (Branch2 a b c) d (Branch2 e f g) h i = branch5 a b c d e f g h i
merge3 (Branch2 a b c) d (Branch3 e f g h i) j k = branch6 a b c d e f g h i j k
merge3 (Branch3 a b c d e) f (Branch2 g h i) j k = branch6 a b c d e f g h i j k
merge3 (Branch3 a b c d e) f (Branch3 g h i j k) l m = branch7 a b c d e f g h i j k l m

treeLookup : (Ord k, DecEq k) => (x : k) -> Tree n k p -> Either (BadKey k) (Maybe (p x))
treeLookup k (Leaf k' v) with (KeyIsBad k k')
  treeLookup k (Leaf k' v) | err with (compare k k')
    treeLookup k (Leaf k' v) | err | EQ with (decEq k k')
      treeLookup k (Leaf k  v) | err | EQ | Yes Refl = Right $ Just v
      treeLookup k (Leaf k' v) | err | EQ | No bad = Left $ err Refl bad
    treeLookup k (Leaf k' v) | err | _ = Right Nothing
treeLookup k (Branch2 t1 k' t2) =
  if k <= k' then
    treeLookup k t1
  else
    treeLookup k t2
treeLookup k (Branch3 t1 k1 t2 k2 t3) =
  if k <= k1 then
    treeLookup k t1
  else if k <= k2 then
    treeLookup k t2
  else
    treeLookup k t3

treeInsert' : Ord k
  => (x : k) -> p x
  -> Tree n k p
  -> Either (Tree n k p) (Tree n k p, k, Tree n k p)
treeInsert' k v (Leaf k' v') =
  case compare k k' of
    LT => Right (Leaf k v, k, Leaf k' v')
    EQ => Left (Leaf k v)
    GT => Right (Leaf k' v', k', Leaf k v)
treeInsert' k v (Branch2 t1 k' t2) =
  if k <= k' then
    case treeInsert' k v t1 of
      Left t1' => Left (Branch2 t1' k' t2)
      Right (a, b, c) => Left (Branch3 a b c k' t2)
  else
    case treeInsert' k v t2 of
      Left t2' => Left (Branch2 t1 k' t2')
      Right (a, b, c) => Left (Branch3 t1 k' a b c)
treeInsert' k v (Branch3 t1 k1 t2 k2 t3) =
  if k <= k1 then
    case treeInsert' k v t1 of
      Left t1' => Left (Branch3 t1' k1 t2 k2 t3)
      Right (a, b, c) => Right (Branch2 a b c, k1, Branch2 t2 k2 t3)
  else
    if k <= k2 then
      case treeInsert' k v t2 of
        Left t2' => Left (Branch3 t1 k1 t2' k2 t3)
        Right (a, b, c) => Right (Branch2 t1 k1 a, b, Branch2 c k2 t3)
    else
      case treeInsert' k v t3 of
        Left t3' => Left (Branch3 t1 k1 t2 k2 t3')
        Right (a, b, c) => Right (Branch2 t1 k1 t2, k2, Branch2 a b c)

treeInsert : Ord k
  => (x : k) -> p x
  -> Tree n k p
  -> Either (Tree n k p) (Tree (S n) k p)
treeInsert k v t =
  case treeInsert' k v t of
    Left t' => Left t'
    Right (a, b, c) => Right (Branch2 a b c)

delType : Nat -> (k : Type) -> (k -> Type) -> Type
delType Z k p = ()
delType (S n) k p = Tree n k p

treeDelete : Ord k => (n : Nat) -> k -> Tree n k p -> Either (Tree n k p) (delType n k p)
treeDelete _ k (Leaf k' v) =
  if k == k' then
    Right ()
  else
    Left (Leaf k' v)
treeDelete (S Z) k (Branch2 t1 k' t2) =
  if k <= k' then
    case treeDelete Z k t1 of
      Left t1' => Left (Branch2 t1' k' t2)
      Right () => Right t2
  else
    case treeDelete Z k t2 of
      Left t2' => Left (Branch2 t1 k' t2')
      Right () => Right t1
treeDelete (S Z) k (Branch3 t1 k1 t2 k2 t3) =
  if k <= k1 then
    case treeDelete Z k t1 of
      Left t1' => Left (Branch3 t1' k1 t2 k2 t3)
      Right () => Left (Branch2 t2 k2 t3)
  else if k <= k2 then
    case treeDelete Z k t2 of
      Left t2' => Left (Branch3 t1 k1 t2' k2 t3)
      Right () => Left (Branch2 t1 k1 t3)
  else
    case treeDelete Z k t3 of
      Left t3' => Left (Branch3 t1 k1 t2 k2 t3')
      Right () => Left (Branch2 t1 k1 t2)
treeDelete (S (S n)) k (Branch2 t1 k' t2) =
  if k <= k' then
    case treeDelete (S n) k t1 of
      Left t1' => Left (Branch2 t1' k' t2)
      Right t1' =>
        case t2 of
          Branch2 a b c => Right (Branch3 t1' k' a b c)
          Branch3 a b c d e => Left (branch4 t1' k' a b c d e)
  else
    case treeDelete (S n) k t2 of
      Left t2' => Left (Branch2 t1 k' t2')
      Right t2' =>
        case t1 of
          Branch2 a b c => Right (Branch3 a b c k' t2')
          Branch3 a b c d e => Left (branch4 a b c d e k' t2')
treeDelete (S (S n)) k (Branch3 t1 k1 t2 k2 t3) =
  if k <= k1 then
    case treeDelete (S n) k t1 of
      Left t1' => Left (Branch3 t1' k1 t2 k2 t3)
      Right t1' => Left (merge1 t1' k1 t2 k2 t3)
  else if k <= k2 then
    case treeDelete (S n) k t2 of
      Left t2' => Left (Branch3 t1 k1 t2' k2 t3)
      Right t2' => Left (merge2 t1 k1 t2' k2 t3)
  else
    case treeDelete (S n) k t3 of
      Left t3' => Left (Branch3 t1 k1 t2 k2 t3')
      Right t3' => Left (merge3 t1 k1 t2 k2 t3')

treeToList : Tree n k p -> List (DPair k p)
treeToList = treeToList' (:: [])
  where
    -- explicit quantification to avoid conflation with {n} from treeToList
    treeToList' : {0 n : Nat} -> (DPair k p -> List (DPair k p)) -> Tree n k p -> List (DPair k p)
    treeToList' cont (Leaf k v) = cont (k ** v)
    treeToList' cont (Branch2 t1 _ t2) = treeToList' (:: treeToList' cont t2) t1
    treeToList' cont (Branch3 t1 _ t2 _ t3) = treeToList' (:: treeToList' (:: treeToList' cont t3) t2) t1

export
data DepMap : (k : Type) -> (k -> Type) -> Type where
  Empty : DepMap k p
  M : (n : Nat) -> Tree n k p -> DepMap k p

export
empty : DepMap k p
empty = Empty

export
lookup : (Ord k, DecEq k)
  => (x : k)
  -> DepMap k p
  -> Either (BadKey k) (Maybe (p x))
lookup _ Empty = Right Nothing
lookup k (M _ t) = treeLookup k t

export
insert : Ord k
  => (x : k) -> p x
  -> DepMap k p
  -> DepMap k p
insert k v Empty = M Z (Leaf k v)
insert k v (M _ t) =
  case treeInsert k v t of
    Left t' => (M _ t')
    Right t' => (M _ t')

export
singleton : Ord k => (x : k) -> p x -> DepMap k p
singleton k v = insert k v empty

export
insertFrom : (Ord k, Foldable f) => f (DPair k p) -> DepMap k p -> DepMap k p
insertFrom = flip $ foldl $ flip insert'
  where insert' : DPair k p -> DepMap k p -> DepMap k p
        insert' (k ** v) = insert k v

export
delete : Ord k => k -> DepMap k p -> DepMap k p
delete _ Empty = Empty
delete k (M Z t) =
  case treeDelete Z k t of
    Left t' => (M _ t')
    Right () => Empty
delete k (M (S n) t) =
  case treeDelete (S n) k t of
    Left t' => (M _ t')
    Right t' => (M _ t')

export
fromList : Ord k => List (DPair k p) -> DepMap k p
fromList l = foldl (flip insert') empty l
  where insert' : DPair k p -> DepMap k p -> DepMap k p
        insert' (k ** v) = insert k v

export
toList : DepMap k p -> List (DPair k p)
toList Empty = []
toList (M _ t) = treeToList t

||| Gets the keys of the map.
export
keys : DepMap k p -> List k
keys = map fst . toList

-- Not really that possible
-- ||| Gets the values of the map. Could contain duplicates.
-- export
-- values : DepMap k v -> List v
-- values = map snd . toList

export
null : DepMap k p -> Bool
null Empty = True
null (M _ _) = False

treeMap : ((x : k) -> a x -> b x) -> Tree n k a -> Tree n k b
treeMap f (Leaf k v) = Leaf k (f k v)
treeMap f (Branch2 t1 k t2) = Branch2 (treeMap f t1) k (treeMap f t2)
treeMap f (Branch3 t1 k1 t2 k2 t3)
    = Branch3 (treeMap f t1) k1 (treeMap f t2) k2 (treeMap f t3)

treeTraverse : Applicative f
  => ((x : k) -> a x -> f (b x))
  -> Tree n k a
  -> f (Tree n k b)
treeTraverse f (Leaf k v) = Leaf k <$> f k v
treeTraverse f (Branch2 t1 k t2) =
  Branch2
    <$> treeTraverse f t1
    <*> pure k
    <*> treeTraverse f t2
treeTraverse f (Branch3 t1 k1 t2 k2 t3) =
  Branch3
    <$> treeTraverse f t1
    <*> pure k1
    <*> treeTraverse f t2
    <*> pure k2
    <*> treeTraverse f t3

||| Not a Functor, but close enough
||| Still a functor from the category of Idris endofunctors to Idris tho?
export
map : ({x : k} -> a x -> b x) -> DepMap k a -> DepMap k b
map _ Empty = Empty
map f (M n t) = M n (treeMap (\k, v => f v) t)

||| Not a traversable, but close enough
export
traverse : Applicative f
  => ({x : k} -> a x -> f (b x))
  -> DepMap k a -> f (DepMap k b)
traverse _ Empty = pure Empty
traverse f (M n t) = M n <$> treeTraverse (\k, v => f v) t

||| Merge two maps. When encountering duplicate keys, using a function to
||| combine the values.
-- TODO: this could totally have better linearity
export
mergeWith : (Ord k, DecEq k)
  => ({x : k} -> p x -> p x -> p x)
  -> DepMap k p
  -> DepMap k p
  -> Either (BadKey k) (DepMap k p)
mergeWith f x y = flip insertFrom x <$> traverse go (toList y)
  where go : DPair k p -> Either (BadKey k) (DPair k p)
        go (a ** v) with (lookup a x)
          go (a ** v) | Left bad = Left bad
          go (a ** v) | Right Nothing = Right (a ** v)
          go (a ** v) | Right (Just v') = Right (a ** f v v')

||| Left-biased merge
-- TODO: lift DecEq requirement? idk
-- would require a lot of work, so prob not
mergeLeft : (Ord k, DecEq k)
  => DepMap k p
  -> DepMap k p
  -> Either (BadKey k) (DepMap k p)
mergeLeft = mergeWith (\x, y => x)
