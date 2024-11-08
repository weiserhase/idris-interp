import Data.Vect
import Data.Fin
mkFin : (n : Nat) -> Fin (S n)
mkFin Z = FZ
mkFin (S k) = FS (mkFin k)
data Tpe: Type where
  Long : Tpe 
  Vd : Tpe
  HeapAdress : Tpe -> Tpe 
%name Tpe t, t1, t2 


data Value: Tpe -> Type where
  LongValue: Int -> Value  Long
  Adress : Fin n -> (t: Tpe) -> Value $ HeapAdress t
  NoValue: Value Vd  
%name Value v, v1, v2 

-- data HeapT: Type where
--   HLong : HeapT
-- %name HeapT ht, ht1, ht2 

data HeapValue: Tpe-> Type where
  BoxedLong : Int -> (HeapValue Long)
%name HeapValue hv, hv1, hv2


Locals : Nat -> Type
Locals n = Vect n Tpe

Operands : Nat -> Type
Operands n = Vect n Tpe

Heap : Nat -> Type
Heap n = Vect n Tpe
-- Heap : Vect n Tpe -> Type
-- Heap ts = Environment ts

-- The Environment that Holds a List of Values of Tpe 
data Environment : Vect n t  -> Type where
  Nil : Environment []
  (::) : (v:Value t) -> Environment ts -> Environment (t :: ts)
%name Environment env, env1, env2 


data Binop : Tpe -> Tpe -> Type where
  Add : Binop Long Long 
%name Binop op, op1, op2 

data Instruction: Locals l -> Operands i -> Heap n ->  Tpe -> Type where
  PushValue: Value v -> Instruction ls (v :: os) hp t -> Instruction ls os hp t
  BinaryOperation: Binop it ot -> Instruction ls (ot:: os) hp t-> Instruction ls (it:: it:: os) hp t  
  Dup: Instruction ls (vt:: vt :: os) hp t-> Instruction ls (vt :: os) hp t
  Return: Instruction ls (t::[]) hp t
  -- Allocate:{addr:Adress}->  Instruction ls (os) (addr::hp) t-> Instruction ls (v::cos) hp t
  Allocate:{t:Tpe}-> Instruction ls (  (HeapAdress t) :: os) (t :: hp) rt -> Instruction ls (t :: os) hp rt
  Load: {t:Tpe} -> (Instruction ls (t::os) hp rt) -> (Instruction ls (HeapAdress t :: os) hp rt)
  Store: {t:Tpe} -> (Instruction ls (os) hp rt) -> (Instruction ls (t::HeapAdress t :: os) hp rt)
  -- Load : {t:Tpe} -> (Instruction ls  v:os )
   
%name Instruction  instr, instr1, instr2   
namespace Hp
  public export 
  data Heap : Vect n Tpe -> Type where
    HNil : Heap []
    (::) : Value t -> Heap ts -> Heap (t :: ts)

-- Heap read function with type safety
heapRead : {ts : Vect n Tpe} ->
           (addr : Fin n) ->
           (heap : Hp.Heap ts) ->
           Value (index addr ts)
heapRead {ts = t :: _} FZ     (v :: _)  = v
heapRead {ts = _ :: ts} (FS k) (_ :: hs) = heapRead {ts = ts} k hs

-- Heap write function with type safety
heapWrite : {ts : Vect n Tpe} ->
            (addr : Fin n) ->
            Value (index addr ts) ->
            Hp.Heap ts ->
            Hp.Heap ts
heapWrite {ts = t :: ts} FZ     v (_ :: hs)  = v :: hs
heapWrite {ts = t :: ts} (FS k) v (h :: hs)  = h :: heapWrite {ts = ts} k v hs

length : Hp.Heap os -> Nat
length HNil = 0
length (v :: xs) = S $ (length xs)

performOp: Binop it ot -> Value it -> Value it ->  Value ot
performOp Add (LongValue n) (LongValue m) = LongValue (n + m)

performBinOp: Binop it ot -> Value it -> Value it ->  Value ot
performBinOp Add (LongValue n) (LongValue m) = LongValue (n + m)

interpret : {hpt : Main.Heap n} ->
            Instruction locals oStack hpt rt ->
            Environment locals ->
            Environment oStack ->
            Hp.Heap hpt ->
            Value rt

-- Handle PushValue, BinaryOperation, Dup, and Return cases as before
interpret (PushValue v instr) ls os hp = interpret instr ls (v :: os) hp
interpret (BinaryOperation op instr) ls (v1 :: v2 :: os) hp = 
    interpret instr ls ((performBinOp op v2 v1) :: os) hp
interpret (Dup instr) ls (v :: os) hp = interpret instr ls (v :: v :: os) hp
interpret (Return) ls (v :: []) hp = v 

-- Allocate case: Allocate a new heap location, push its address onto the operand stack
interpret {hpt} (Allocate {t} instr) ls (v::os) hp =
    let newAddr = mkFin (length hp)  -- Address of the newly allocated location
        addrValue = Adress newAddr t -- Address as a `Value` of type `HeapAdress t`
        newHp = v :: hp     -- Extend the heap with the new default value
    in interpret instr ls (addrValue :: os) newHp

-- Load case: Load the value at the address from the heap and push it onto the operand stack
interpret (Load instr) ls (Adress addr t :: os) hp =
    let v = heapRead addr hp
    in interpret instr ls (v :: os) hp

-- Store case: Pop a value and address, write the value to the heap at the specified address
interpret (Store instr) ls (v :: Adress addr t :: os) hp =
    let newHp = heapWrite addr v hp
    in interpret instr ls os newHp

InterpFull : Instruction [] [] [] t-> Value t
InterpFull  instr = interpret instr [] [] Hp.HNil


example: Instruction [] []  [] Long
example = PushValue (LongValue 12) $ Dup $ BinaryOperation Add $  Return 


exampleAllocate : Instruction [] [] [] $HeapAdress Long 
exampleAllocate = PushValue (LongValue 42) $  
                  Allocate $ 
                  Return
                  
e: Value Long
e = InterpFull example

e'= (InterpFull exampleAllocate)
