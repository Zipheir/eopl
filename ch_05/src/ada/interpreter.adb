with Ada.Text_IO;
with Ada.Integer_Text_IO;

package body Interpreter is
  -- Environments

  function Extend_Env(V: in Variable; A: in Exp_Val; E: in Env_Ptr)
      return Env_Ptr is
    F: Env_Ptr;
  begin
    F := new Frame'(Var => V, Val => A, Rest => E);
    return F;
  end Extend_Env;

  function Apply_Env(E: in Env_Ptr; V: in Variable) return Exp_Val is
    P: Env_Ptr := E;
  begin
    if P = null then
      Report_No_Binding_Found(V);
    end if;

    if P.Var = V then
      return P.Val;
    else
      return Apply_Env(P.Rest, V);
    end if;
  end Apply_Env;

  procedure Report_No_Binding_Found(V: in Variable) is
    package Var_IO is new Ada.Text_IO.Enumeration_IO (Enum => Variable);
  begin
    Ada.Text_IO.Put("No binding found for variable ");
    Var_IO.Put(V);
    raise No_Binding_Error;
  end Report_No_Binding_Found;

  -- TODO
  function Init_Env return Env_Ptr is
  begin
    return null;
  end Init_Env;

  -- Expressed values

  function Make_Num_Val(N: in Integer) return Exp_Val is
    V: Exp_Val(Num_Val);
  begin
    V.Num := N;
    return V;
  end Make_Num_Val;

  function Make_Bool_Val(B: in Boolean) return Exp_Val is
    V: Exp_Val(Bool_Val);
  begin
    V.Bool := B;
    return V;
  end Make_Bool_Val;

  function Make_Proc_Val(P: in Proc) return Exp_Val is
    V: Exp_Val(Proc_Val);
  begin
    V.Proc1 := P;
    return V;
  end Make_Proc_Val;

  -- Extractors

  function Exp_Val_to_Num(V: in Exp_Val) return Integer is
  begin
    return V.Num;
  end Exp_Val_to_Num;

  function Exp_Val_to_Bool(V: in Exp_Val) return Boolean is
  begin
    return V.Bool;
  end Exp_Val_to_Bool;

  function Exp_Val_to_Proc(V: in Exp_Val) return Proc is
  begin
    return V.Proc1;
  end Exp_Val_to_Proc;

  -- Registers

  Exp_Register: Expr_Ptr;
  Val_Register: Exp_Val;
  Cont_Register: array (Integer range 0 .. 256) of Cont_Ptr;
  Env_Register: Env_Ptr;
  Proc1_Register: Proc;

  -- Value display

  procedure Print_Value_Register is
    package Boolean_IO is new Ada.Text_IO.Enumeration_IO (Enum => Boolean);
  begin
    case Val_Register.Kind is
      when Num_Val =>
        Ada.Integer_Text_IO.Put(Val_Register.Num);
      when Bool_Val =>
        Boolean_IO.Put(Val_Register.Bool);
      when Proc_Val =>
        Ada.Text_IO.Put("<procedure>");
    end case;
    Ada.Text_IO.New_Line;
  end Print_Value_Register;

  -- Continuation stack management.

  Cont_Stack_Index : Integer := 0;

  procedure Push_Cont(K: in Cont_Ptr) is
  begin
    Cont_Register(Cont_Stack_Index) := K;
    Cont_Stack_Index := Cont_Stack_Index + 1;
  end Push_Cont;

  function Pop_Cont return Cont_Ptr is
    K: Cont_Ptr;
  begin
    K := Cont_Register(Cont_Stack_Index);
    Cont_Stack_Index := Cont_Stack_Index - 1;
    return K;
  end Pop_Cont;

  -- Cont_Register is assumed to hold the rest of the continuation
  -- stack.
  procedure Apply_Cont(K: in Cont_Ptr) is
    Next: Cont_Ptr;
  begin
    case K.Kind is
      when Rator_Cont =>
        Next := new Cont'(Rand_Cont, Val_Register);
        Push_Cont(Next);
        Env_Register := K.Env;
        Exp_Register := K.Rand;
        Value_Of;
      when Rand_Cont =>
        Proc1_Register := Exp_Val_to_Proc(K.Rator_Val);
        Apply_Procedure;
      when others =>
        Ada.Text_IO.Put_Line("Empty continuation!");
        raise Continuation_Error;
    end case;
  end Apply_Cont;

  procedure Continue is
    K : Cont_Ptr;
  begin
    if Cont_Stack_Index < 0 then
      Print_Value_Register;
      Ada.Text_IO.Put_Line("End of computation.");
    else
      K := Pop_Cont;
      Apply_Cont(K);
    end if;
  end Continue;

  procedure Apply_Procedure is
  begin
    Exp_Register := Proc1_Register.PBody;
    Env_Register := Extend_Env(Proc1_Register.Bound_Var, Val_Register,
                      Proc1_Register.Saved_Env);
    Value_Of;
  end Apply_Procedure;

  procedure Value_Of is
    E: Expr_Ptr := Exp_Register;
    Next: Cont_Ptr;
    P: Proc;
  begin
    case E.Kind is
      when Const_Exp =>
        Val_Register := Make_Num_Val(E.Num);
        Continue;
      when Proc_Exp =>
        P.Bound_Var := E.Bound_Var;
        P.PBody := E.PBody;
        Val_Register := Make_Proc_Val(P);
        Continue;
      when Call_Exp =>
        Next := new Cont'(Rator_Cont, E.Rand, Env_Register);
        Push_Cont(Next);
        Exp_Register := E.Rator;
        Value_Of;
    end case;
  end Value_Of;

  procedure Value_of_Program(E: in Expr_Ptr) is
  begin
    Cont_Stack_Index := 0;
    Exp_Register := E;
    Env_Register := Init_Env;
    Value_Of;
  end Value_of_Program;

end Interpreter;
