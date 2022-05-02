package Interpreter is
  -- A la BASIC.
  type Variable is new Character;

  -- Procedures

  type Expression(<>);
  type Expr_Ptr is access Expression;
  type Frame;
  type Env_Ptr is access Frame;

  type Proc is
    record
      Bound_Var: Variable;
      PBody: Expr_Ptr;
      Saved_Env: Env_Ptr;
    end record;

  type Exp_Val_Kind is (Num_Val, Bool_Val, Proc_Val);

  type Exp_Val(Kind: Exp_Val_Kind := Num_Val) is
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
  procedure Print_Value_Register;

  -- Environments
  -- It would be nice to use a general list type here.

  type Frame is
    record
      Var: Variable;
      Val: Exp_Val;
      Rest: Env_Ptr;
    end record;

  function Extend_Env(V: in Variable; A: in Exp_Val; E: in Env_Ptr)
    return Env_Ptr;
  function Apply_Env(E: in Env_Ptr; V: in Variable) return Exp_Val;
  function Init_Env return Env_Ptr;
  procedure Report_No_Binding_Found(V: in Variable);

  No_Binding_Error: exception;

  type Expr_Kind is (Const_Exp, Var_Exp, ZeroP_Exp, Proc_Exp,
                     Call_Exp);

  type Expression(Kind: Expr_Kind) is
    record
      case Kind is
        when Const_Exp =>
          Num: Integer;
        when Var_Exp =>
          Var: Variable;
        when ZeroP_Exp =>
          ZExp: Expr_Ptr;
        when Proc_Exp =>
          Bound_Var: Variable;
          PBody: Expr_Ptr;
        when Call_Exp =>
          Rator: Expr_Ptr;
          Rand: Expr_Ptr;
      end case;
    end record;

  type Cont_Kind is (Empty_Cont, Zero1_Cont, Rator_Cont, Rand_Cont);
  type Cont(<>);
  type Cont_Ptr is access Cont;
  type Cont(Kind: Cont_Kind := Empty_Cont) is
    record
      Env: Env_Ptr;
      case Kind is
        when Zero1_Cont =>
          ZKont: Cont_Ptr;
        when Rator_Cont =>
          Rand: Expr_Ptr;
        when Rand_Cont =>
          Rator_Val: Exp_Val;
        when others =>
          null;
      end case;
    end record;

  Continuation_Error: exception;

  procedure Push_Cont(K: in Cont_Ptr);
  function Pop_Cont return Cont_Ptr;
  function Current_Cont return Cont_Ptr;
  procedure Apply_Cont;
  procedure Apply_Procedure;
  procedure Value_Of;
  procedure Value_of_Program(E: in Expr_Ptr);
end Interpreter;
