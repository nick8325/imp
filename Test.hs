--import Prelude hiding (map)

data Ordinal = ZeroOrd | SuccOrd Ordinal | Lim [Ordinal] --(Stream Ordinal)

--data Stream a = Cons a (Stream a)
--
--map :: (a -> b) -> Stream a -> Stream b
--map f (Cons x xs) = Cons (f x) (map f xs)

(+++) :: Ordinal -> Ordinal -> Ordinal
x +++ ZeroOrd = x
x +++ SuccOrd y = SuccOrd (x +++ y)
x +++ Lim f = Lim (map (x +++) f)

(***) :: Ordinal -> Ordinal -> Ordinal
x *** ZeroOrd = ZeroOrd
x *** SuccOrd y = (x *** y) +++ x
x *** Lim xs = Lim (map (x ***) xs)

infinity :: Ordinal
infinity = Lim (inf ZeroOrd)
  where
    inf x = x:inf (SuccOrd x)
