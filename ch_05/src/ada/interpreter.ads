package Interpreter is
  type Variable is new Character;

  -- Procedures

  type Expression;
  type Expr_Ptr is access Expression;

  type Proc is
    record
      Bound_Var: Variable;
      PBody: Expr_Ptr;
      Saved_Env: Env_Ptr;
    end record;

  type Exp_Val_Kind is (Num_Val, Bool_Val, Proc_Val);

  type Exp_Val(Kind: Exp_Val_Kind) is
    record
      case Kind is
        when Num_Val =>
          Num: Integer;
        when Bool_Val =>
          Bool: Boolean;
        when Proc_Val =>
          Proc1: Proc;
      end case;
    end record;

  function Make_Num_Val(N: in Integer) return Exp_Val;
  function Make_Bool_Val(B: in Boolean) return Exp_Val;
  function Make_Proc_Val(P: in Proc) return Exp_Val;
  function Exp_Val_to_Num(V: in Exp_Val) return Integer;
  function Exp_Val_to_Bool(V: in Exp_Val) return Boolean;
  function Exp_Val_to_Proc(V: in Exp_Val) return Proc;

   type Frame is
    record
      Var: Variable;
      Val: Exp_Val;
    end record;

  package My_Lists is new Lists(Frame); use My_Lists;
  type Environment is new List;
  type Env_Ptr is access Environment;

  function Extend_Env(V: Variable, A: Exp_Val, E: Env_Ptr) return Env_Ptr;
  function Apply_Env(E: Env_Ptr, V: Variable) return Value;
  function Init_Env return Env_Ptr;

  type Expr_Kind is (Const_Exp, Var_Exp, Diff_Exp, Proc_Exp, Call_Exp);

  type Expression(Kind: Expr_Kind) is
    record
      case Kind is
        when Const_Exp =>
          Num: Integer;
        when Proc_Exp =>
          Bound_Var: Variable;
          PBody: Expr_Ptr;
        when Call_Exp =>
          Rator: Expr_Ptr;
          Rand: Expr_Ptr;
      end case;
    end record;
  
  type Cont_Kind is (Rator_Cont, Rand_Cont);
  
  type Cont(Kind: Cont_Kind := End_Cont) is
    record
      case Kind is
        when Rator_Cont =>
          Rand: Expr_Ptr;
          Env: Env_Ptr;
        when Rand_Cont =>
          Rator_Val: Exp_Val;
      end case;
    end record;
    
  type Cont_Ptr is access Cont;

  procedure Apply_Cont(K: in Cont_Ptr);
  procedure Continue;
  procedure Apply_Procedure;
  procedure Value_Of;
  procedure Value_of_Program(E: in Expr_Ptr);
end Interpreter;
