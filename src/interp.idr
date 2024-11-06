import Data.Vect
data Tpe: Type where
  Long : Tpe 
  Vd : Tpe
%name Tpe t, t1, t2 

data Value: Tpe -> Type where
  LongValue: Int -> Value  Long
  NoValue: Value Vd  
%name Value v, v1, v2 

Locals : Nat -> Type
Locals n = Vect n Tpe

Operands : Nat -> Type
Operands n = Vect n Tpe

-- The Environment that Holds a List of Values of Tpe 
data Environment : Vect n t  -> Type where
  Nil : Environment []
  (::) : (v:Value t) -> Environment ts -> Environment (t :: ts)
%name Environment env, env1, env2 

data Binop : Tpe -> Tpe -> Type where
  Add : Binop Long Long 
%name Binop op, op1, op2 

data Instruction: Locals l -> Operands i -> Tpe -> Type where
  PushValue: Value v -> Instruction ls (v :: os) t -> Instruction ls os t
  BinaryOperation: Binop it ot -> Instruction ls (ot:: os) t -> Instruction ls (it:: it:: os) t   
  Dup: Instruction ls (vt:: vt :: os) t -> Instruction ls (vt :: os) t     
  Return: Instruction ls (t::[]) t 
%name Instruction  instr, instr1, instr2   


performOp: Binop it ot -> Value it -> Value it ->  Value ot
performOp Add (LongValue n) (LongValue m) = LongValue (n + m)

performBinOp: Binop it ot -> Value it -> Value it ->  Value ot
performBinOp Add (LongValue n) (LongValue m) = LongValue (n + m)

interpret: Instruction locals oStack rt -> Environment locals -> Environment oStack -> Value rt
interpret (PushValue v instr) ls  os = interpret instr ls (v::os) 
interpret (BinaryOperation op instr) ls (v1:: v2::  os) = interpret instr ls $ (performBinOp op v2 v1) :: os 
interpret (Dup instr) ls (v :: os) = interpret instr ls (v:: v::os)
interpret (Return ) ls (v :: []) =  v

InterpFull : Instruction [] [] t -> Value t
InterpFull  instr = interpret instr [] []


example: Instruction [] [] Long
example = PushValue (LongValue 12) $ Dup $ BinaryOperation Add $  Return 


e: Value Long
e = interpret example [] []
