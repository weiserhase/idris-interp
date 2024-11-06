data Lst : Nat -> Type -> Type where
  Nil : Lst Z a
  (::) : a -> Lst n a -> Lst (n) a

(++) : Lst n a -> Lst m a -> Lst (n + m) a
(++) Nil ys = ys
(++) (x :: xs) ys = x :: (xs ++ ys)

-- Helper Lemmas
plusZeroRightNeutral : (n : Nat) -> n + Z = n
plusZeroRightNeutral Z = Refl
plusZeroRightNeutral (S n) = cong S (plusZeroRightNeutral n)

plusSuccRight : (n : Nat) -> (m : Nat) -> n + S m = S (n + m)
plusSuccRight Z m = Refl
plusSuccRight (S n) m = cong S (plusSuccRight n m)

-- Commutativity of Addition using rewrite
lemma : (n : Nat) -> (m : Nat) -> n + m = m + n
lemma Z m = sym (plusZeroRightNeutral m)
lemma (S n) m =
  rewrite cong S (lemma n m) in
  rewrite sym (plusSuccRight m n) in
  Refl
