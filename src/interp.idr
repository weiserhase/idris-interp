import Data.Vect
import Data.Fin

data Index : Vect n t -> t -> Type where
  Z : Index (x :: xs) x
  S : Index xs x -> Index (y :: xs) x

%name Index idx, idx'

-- -- Helper function to get the last element of a non-empty vector
-- last : Vect (S len) t -> t
-- last (x :: []) = x
-- last (_ :: x :: xs) = Main.last (x :: xs)
--
-- Function to create an index pointing to the last element of a vector
mkIndex : (xs : Vect (S n) t) -> Index xs (last xs)
mkIndex (x :: []) = Z
mkIndex (_ :: x :: xs) = S (mkIndex (x :: xs))

-- Additional Helper
mkFin : (n : Nat) -> Fin (S n)
mkFin Z = FZ
mkFin (S k) = FS (mkFin k)

data Tpe : Type where
  Long : Tpe
  Vd : Tpe
  HeapAdress : Tpe -> Tpe

%name Tpe t, t1, t2

data Value : Tpe -> Type where
  LongValue : Int -> Value Long
  Adress : Index hpt t -> (t:Tpe)-> Value (HeapAdress t)
  NoValue : Value Vd

%name Value v, v1, v2

data HeapValue : Tpe -> Type where
  BoxedLong : Int -> (HeapValue Long)

%name HeapValue hv, hv1, hv2

Locals : Nat -> Type
Locals n = Vect n Tpe

Operands : Nat -> Type
Operands n = Vect n Tpe

Heap : Nat -> Type
Heap n = Vect n Tpe

-- The Environment that Holds a List of Values of Tpe
data Environment : Vect n t -> Type where
  Nil : Environment []
  (::) : (v : Value t) -> Environment ts -> Environment (t :: ts)

%name Environment env, env1, env2

data Binop : Tpe -> Tpe -> Type where
  Add : Binop Long Long

%name Binop op, op1, op2

data Instruction : Locals l -> Operands i -> Heap n -> Tpe -> Type where
  PushValue : Value v -> Instruction ls (v :: os) hp t -> Instruction ls os hp t
  BinaryOperation : Binop it ot -> Instruction ls (ot :: os) hp t -> Instruction ls (it :: it :: os) hp t
  Dup : Instruction ls (vt :: vt :: os) hp t -> Instruction ls (vt :: os) hp t
  Return : Instruction ls (t :: []) hp t
  Allocate : {t : Tpe} -> Instruction ls ((HeapAdress t) :: os) (t :: hp) rt -> Instruction ls (t :: os) hp rt
  -- Load : {t : Tpe} -> (Instruction ls (t :: os) hp rt) -> Instruction ls ((HeapAdress t) :: os) hp rt
  Load : {tp : Tpe} -> 
         (Instruction ls (tp :: os) hp rt) -> 
         Instruction ls ((HeapAdress tp) :: os) hp rt
  Store : {t : Tpe} -> (Instruction ls os hp rt) -> Instruction ls (t :: (HeapAdress t) :: os) hp rt

%name Instruction instr, instr1, instr2

namespace Hp
  public export
  data Heap : Vect n Tpe -> Type where
    Nil : Heap []
    (::) : Value t -> Heap ts -> Heap (t :: ts)

mkHpIndex : (xs : Hp.Heap ts)->  Index ts (last ts)
mkHpIndex (x :: [])  = Z
mkHpIndex (_ :: x :: xs)  = S (mkHpIndex (x :: xs))

-- Heap read function with type safety
heapRead : {ts : Vect n Tpe} ->
           (addr : Index ts k) ->
           (heap : Hp.Heap ts) ->
           Value k
heapRead Z (v :: os) = v
heapRead (S addr) (v :: xs) = heapRead addr xs

-- Heap write function with type safety
heapWrite : {ts : Vect n Tpe} ->
            (addr : Index ts k) ->
            Value k ->
            Hp.Heap ts ->
            Hp.Heap ts
heapWrite Z v (v1 :: xs) = v :: xs
heapWrite (S idx) v (v1 :: xs) = v1 :: heapWrite idx v xs

length : Hp.Heap os -> Nat
length Nil = 0
length (v :: xs) = S (length xs)

performOp : Binop it ot -> Value it -> Value it -> Value ot
performOp Add (LongValue n) (LongValue m) = LongValue (n + m)

performBinOp : Binop it ot -> Value it -> Value it -> Value ot
performBinOp Add (LongValue n) (LongValue m) = LongValue (n + m)
interpret : {hpt : Main.Heap n} ->
            Instruction locals oStack hpt rt ->
            Environment locals ->
            Environment oStack ->
            Hp.Heap hpt ->
            Value rt
interpret (PushValue v instr) ls os hp = interpret instr ls (v :: os) hp
interpret (BinaryOperation op instr) ls (v1 :: v2 :: os) hp = 
    interpret instr ls ((performBinOp op v2 v1) :: os) hp
interpret (Dup instr) ls (v :: os) hp = interpret instr ls (v :: v :: os) hp
interpret (Return) ls (v :: []) hp = v

interpret {hpt} (Allocate {t} instr) ls (v :: os) hp =
    let newHp = v :: hp
        newAddr = mkHpIndex newHp
        addrValue = Adress newAddr t
    in interpret instr ls (addrValue :: os) newHp

-- Load case: Load the value at the address from the heap and push it onto the operand stack
-- interpret (Load instr) ls (add@(Adress addr l)  :: os) hp =
--     let v = heapRead ?addr hp
--     in interpret instr ls (v :: os) hp
interpret (Load {tp} instr) ls (Adress addr tp :: os) hp =
    let v = heapRead ?addr hp
    in interpret instr ls (v :: os) hp
-- Store case: Pop a value and address, write the value to the heap at the specified address
interpret (Store instr) ls (v :: Adress addr t :: os) hp =
    let newHp = heapWrite addr v hp
    in interpret instr ls os newHp


InterpFull : Instruction [] [] [] t -> Value t
InterpFull instr = interpret instr [] [] []

-- Example Instructions
example : Instruction [] [] [] Long
example = PushValue (LongValue 12) $ Dup $ BinaryOperation Add $ Return

exampleAllocate : Instruction [] [] [] (HeapAdress Long)
exampleAllocate = PushValue (LongValue 42) $
                  Allocate $
                  Return

e : Value Long
e = InterpFull example

e' = InterpFull exampleAllocate
