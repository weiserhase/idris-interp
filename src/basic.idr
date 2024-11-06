-- plusZeroRightNeutral : (n : Nat) -> n + Z = n
-- plusZeroRightNeutral Z = Refl
--plusZeroRightNeutral (S n) = cong S (plusZeroRightNeutral n)
--
-- plusSuccRight : (n : Nat) -> (m : Nat) -> n + S m = S (n + m)
-- plusSuccRight Z m = Refl
-- plusSuccRight (S n) m = cong S (plusSuccRight n m)
--
-- -- Commutativity of Addition using rewrite
-- lemma : (n : Nat) -> (m : Nat) -> n + m = m + n
-- lemma Z m = sym (plusZeroRightNeutral m)
-- lemma (S n) m =
--   rewrite cong S (lemma n m) in
--   rewrite sym (plusSuccRight m n) in
--   Refl

pzrn: ( n:Nat ) -> n + 0 = n
pzrn Z = Refl
pzrn (S k) = cong S (pzrn k)

psl : (k : Nat) -> (n : Nat) -> (S k) + n = S (k + n)
psl k n = Refl

psr: (n: Nat) -> (m: Nat) -> n + S m = S (n+m)
psr 0 m = Refl
psr (S k) m = cong S (psr k m) 

psr': (n: Nat) -> (m: Nat) ->  S (n+m) = n + S m 
psr' 0 m = Refl
psr' (S k) m = cong S (psr' k m) 

psc: (n:Nat)-> (m:Nat)-> S n +m = n + S m
psc 0 m = Refl 
psc (S k) m = cong S (psc k m)

data Tpe : Type where
  Vd: Tpe
  Long : Tpe

data Value : Tpe -> Type where
  LongValue : Int -> Value Long
  NoValue: Value Vd 


data Lst: Nat -> Type  -> Type where
  Nil : Lst 0 a 
  (::) : a -> (Lst n a)-> Lst (S n)  a

(++) : Lst n a -> Lst m a -> Lst (n + m) a
(++) Nil ys = ys
(++) (x :: xs) ys = x :: (xs ++ ys)




-- lemma (S n) m =
--   rewrite cong S (lemma n m) in  
--   rewrite sym (plusSuccRight m n) in  
--     Refl 
