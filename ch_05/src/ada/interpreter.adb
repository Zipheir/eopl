with Ada.Text_IO;
with Ada.Integer_Text_IO;

package body Interpreter is
  -- Environments

  function Extend_Env(V: in Variable; A: in Exp_Val; E: in Env_Ptr)
      return Env_Ptr is
    F: Env_Ptr;
  begin
    F := new Frame'(Kind => Normal, Var => V, Val => A, Rest => E);
    return F;
  end Extend_Env;

  function Extend_Env_Rec(Name: in Variable; V: in Variable;
      B: in Expr_Ptr; E: in Env_Ptr) return Env_Ptr is
    EP: Env_Ptr;
  begin
    EP := new Frame'(Kind => Recursive, Name => Name, BVar => V,
            PBody => B, Rest => E);
    return EP;
  end Extend_Env_Rec;

  function Apply_Env(E: in Env_Ptr; V: in Variable) return Exp_Val is
    EP: Env_Ptr := E;
    F: Proc;
  begin
    if EP = null then
      Report_No_Binding_Found(V);
    end if;

    case EP.Kind is
      when Normal =>
        if EP.Var = V then
          return EP.Val;
        else
          return Apply_Env(EP.Rest, V);
        end if;
      when Recursive =>
        if EP.Name = V then
          F.Bound_Var := EP.BVar;
          F.PBody := EP.PBody;
          F.Saved_Env := EP;
          return Make_Proc_Val(F);
        else
          return Apply_Env(EP.Rest, V);
        end if;
    end case;
  end Apply_Env;

  procedure Report_No_Binding_Found(V: in Variable) is
    package Var_IO is new Ada.Text_IO.Enumeration_IO (Enum => Variable);
  begin
    Ada.Text_IO.Put("No binding found for variable ");
    Var_IO.Put(V);
    raise No_Binding_Error;
  end Report_No_Binding_Found;

  function Init_Env return Env_Ptr is
  begin
    return Extend_Env('I', Make_Num_Val(1),
             Extend_Env('V', Make_Num_Val(5),
               Extend_Env('X', Make_Num_Val(10), null)));
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
    package Kind_IO is new Ada.Text_IO.Enumeration_IO (Enum => Cont_Kind);
    Old_SP: Integer := Cont_Stack_Index;
  begin
    Cont_Register(Cont_Stack_Index) := K;
    Cont_Stack_Index := Cont_Stack_Index + 1;
    Ada.Text_IO.Put("Continuation push, stack next free is now ");
    Ada.Integer_Text_IO.Put(Cont_Stack_Index, 0);
    Ada.Text_IO.New_Line;
    Ada.Text_IO.Put("Top continuation is of type ");
    Kind_IO.Put(Cont_Register(Old_Sp).Kind);
    Ada.Text_IO.New_Line;
  end Push_Cont;

  function Pop_Cont return Cont_Ptr is
    K: Cont_Ptr;
  begin
    Cont_Stack_Index := Cont_Stack_Index - 1;
    K := Cont_Register(Cont_Stack_Index);
    return K;
  end Pop_Cont;

  function Current_Cont return Cont_Ptr is
  begin
    return Cont_Register(Cont_Stack_Index - 1);
  end Current_Cont;

  -- Cont_Register is assumed to hold the rest of the continuation
  -- stack.
  procedure Apply_Cont is
    K, Next: Cont_Ptr;
    M, N: Integer;
  begin
    K := Pop_Cont;
    case K.Kind is
      when Empty_Cont =>
        Print_Value_Register;
        Ada.Text_IO.Put_Line("End of computation.");
      when Zero1_Cont =>
        Push_Cont(K.ZKont);
        N := Exp_Val_to_Num(Val_Register);
        if N = 0 then
          Val_Register := Make_Bool_Val(True);
        else
          Val_Register := Make_Bool_Val(False);
        end if;
        Apply_Cont;
      when Diff1_Cont =>
        Next := new Cont'(Diff2_Cont, null, Val_Register, K.D1Kont);
        Push_Cont(Next);
        Exp_Register := K.DExp;
        Env_Register := K.Env;
        Value_Of;
      when Diff2_Cont =>
        Push_Cont(K.D2Kont);
        M := Exp_Val_to_Num(K.DVal);
        N := Exp_Val_to_Num(Val_Register);
        Val_Register := Make_Num_Val(M - N);
        Apply_Cont;
      when Rator_Cont =>
        Next := new Cont'(Rand_Cont, null, Val_Register, K.TKont);
        Push_Cont(Next);
        Env_Register := K.Env;
        Exp_Register := K.Rand;
        Value_Of;
      when Rand_Cont =>
        Push_Cont(K.AKont);
        Proc1_Register := Exp_Val_to_Proc(K.Rator_Val);
        Apply_Procedure;
      when Let_Exp_Cont =>
        Push_Cont(K.LKont);
        Exp_Register := K.LBody;
        Env_Register := Extend_Env(K.LVar, Val_Register, K.Env);
        Value_Of;
      when If_Test_Cont =>
        Push_Cont(K.IKont);
        if Exp_Val_to_Bool(Val_Register) then
          Exp_Register := K.Con;
        else
          Exp_Register := K.Alt;
        end if;
        Env_Register := K.Env;
        Value_Of;
    end case;
  end Apply_Cont;

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
        Apply_Cont;
      when Var_Exp =>
        Val_Register := Apply_Env(Env_Register, E.Var);
        Apply_Cont;
      when ZeroP_Exp =>
        Next := new Cont'(Zero1_Cont, null, Current_Cont);
        Push_Cont(Next);
        Exp_Register := E.ZExp;
        Value_Of;
      when Diff_Exp =>
        Next := new Cont'(Diff1_Cont, Env_Register, E.DExp2,
                  Current_Cont);
        Push_Cont(Next);
        Exp_Register := E.DExp1;
        Value_Of;
      when Proc_Exp =>
        P.Bound_Var := E.Bound_Var;
        P.PBody := E.PBody;
        Val_Register := Make_Proc_Val(P);
        Apply_Cont;
      when Let_Exp =>
        Next := new Cont'(Let_Exp_Cont, Env_Register, E.LVar, E.LBody,
                  Current_Cont);
        Push_Cont(Next);
        Exp_Register := E.LExp;
        Value_Of;
      when Letrec_Exp =>
        Exp_Register := E.LR_Body;
        Env_Register := Extend_Env_Rec(E.PName, E.LR_BVar, E.LR_PBody,
                          Env_Register);
        Value_Of;
      when If_Exp =>
        Next := new Cont'(If_Test_Cont, Env_Register, E.Con, E.Alt,
                  Current_Cont);
        Push_Cont(Next);
        Exp_Register := E.Test;
        Value_Of;
      when Call_Exp =>
        Next := new Cont'(Rator_Cont, Env_Register, E.Rand,
                  Current_Cont);
        Push_Cont(Next);
        Exp_Register := E.Rator;
        Value_Of;
    end case;
  end Value_Of;

  function Value_of_Program(E: in Expr_Ptr) return Exp_Val is
  begin
    Cont_Stack_Index := 0;
    Push_Cont(new Cont(Empty_Cont));
    Exp_Register := E;
    Env_Register := Init_Env;
    Value_Of;
    return Val_Register;
  end Value_of_Program;

end Interpreter;
