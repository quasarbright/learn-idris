module Main

import Data.Vect



nums : Vect 3 Integer
nums = [1,2,3]

-- foldrv : {n : Nat} -> (a -> b -> b) -> b -> Vect n a -> b
-- foldrv f b Nil = b
-- foldrv f b (x :: xs) = f x (foldrv f b xs)

filterv : (a -> Bool) -> Vect n a -> (m ** Vect m a)
filterv p Nil = (0 ** Nil)
filterv p (x :: xs) with (filter p xs)
    | (_ ** xs') = if (p x) then (_ ** x :: xs') else (_ ** xs')
-- filterv p (x :: xs) with (filter p xs) | (n ** xs') = if (p x) then ((S n) ** x :: xs') else (n ** xs')

-- Nil : Int
-- Nil = 0

-- (::) : Int -> Int -> Int
-- (::) = (+)

-- num : Int
-- num = [1,2,3] -- evaluates to 6 lol

using (a:Type, b:Type, c:Type)
    data Composition : Type -> Type -> Type where
        Singleton : (a -> b) -> Composition a b
        Compose : Composition a b -> Composition b c -> Composition a c

toFunction : Composition a b -> a -> b
toFunction (Singleton f) = f
toFunction (Compose f g) = toFunction g . toFunction f

Nil : Composition a a
Nil = Singleton id

(::) : (a -> b) -> Composition b c -> Composition a c
(::) f c = Singleton f `Compose` c
 
applyComposition : Composition a b -> a -> b
applyComposition f a = toFunction f $ a

main : IO ()
main = putStrLn "Hello world"


-- proofs

nat_induction : (P : Nat -> Type) ->             -- Property to show
                (P Z) ->                         -- Base case
                ((k : Nat) -> P k -> P (S k)) -> -- Inductive step
                (x : Nat) ->                     -- Show for all x
                P x
nat_induction P pz ind Z = pz
nat_induction P pz ind (S n) = ind n (nat_induction P pz ind n)

total
plus_commutes_rhs_z : (m : Nat) -> m = plus m 0
plus_commutes_rhs_z Z = Refl
plus_commutes_rhs_z (S k) = cong (plus_commutes_rhs_z k)


total
plus_commutes_s : (k : Nat) -> (m : Nat) -> S (plus m k) = plus m (S k)
plus_commutes_s k Z = Refl
plus_commutes_s k (S m) = rewrite plus_commutes_s k m in Refl

total
plus_commutes : (n : Nat) -> (m : Nat) -> n + m = m + n
plus_commutes Z m = plus_commutes_rhs_z m
plus_commutes (S k) m = rewrite plus_commutes k m in plus_commutes_s k m

plusReducesZ' : (n:Nat) -> n = plus n Z
plusReducesZ' Z     = ?plusredZ_Z
plusReducesZ' (S k) = let ih = plusReducesZ' k in
                      ?plusredZ_S
