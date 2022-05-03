with Ada.Text_IO; use Ada.Text_IO;
with Ada.Integer_Text_IO;
with Interpreter; use Interpreter;

-- Very basic test framework.

procedure Run_Tests is
  procedure Test_Num_Exp(Name: in String; Expect: in Integer;
              Expr: in Expr_Ptr) is
    Result: Exp_Val := Value_of_Program(Expr);
  begin
    if Exp_Val_to_Num(Result) = Expect then
      Put_Line("Test passed: " & Name);
    else
      Put_Line("Test FAILED: " & Name);
      Put("Expected ");
      Ada.Integer_Text_IO.Put(Expect, 0);
      Put(", got ");
      Ada.Integer_Text_IO.Put(Exp_Val_to_Num(Result));
      New_Line;
    end if;
  end Test_Num_Exp;

  E: Expr_Ptr;
  Add1: Expr_Ptr;
begin
  -- Utility +1 procedure expression.
  Add1 := new Expression'(Proc_Exp, 'A',
            new Expression'(Diff_Exp,
              new Expression'(Var_Exp, 'A'),
              new Expression'(Const_Exp, -1)));

  E := new Expression'(Const_Exp, 4);
  Test_Num_Exp("constant", 4, E);

  E := new Expression'(Var_Exp, 'X');
  Test_Num_Exp("variable", 10, E);

  E := new Expression'(Call_Exp, Add1,
         new Expression'(Const_Exp, 4));
  Test_Num_Exp("application", 5, E);

  E := new Expression'(Diff_Exp,
           new Expression'(Const_Exp, 5),
           new Expression'(Const_Exp, 2));
  Test_Num_Exp("diff constants", 3, E);

  E := new Expression'(Diff_Exp,
           new Expression'(Var_Exp, 'X'),
           new Expression'(Var_Exp, 'I'));
  Test_Num_Exp("diff variables", 9, E);

  -- let A = 4 in A
  E := new Expression'(Let_Exp, 'A',
        new Expression'(Const_Exp, 4),
        new Expression'(Var_Exp, 'A'));
  Test_Num_Exp("let constant", 4, E);

  -- let A = (add1 X) in -(A, X)
  E := new Expression'(Let_Exp, 'A',
         new Expression'(Call_Exp, Add1,
           new Expression'(Var_Exp, 'X')),
         new Expression'(Diff_Exp,
           new Expression'(Var_Exp, 'A'),
           new Expression'(Var_Exp, 'X')));
  Test_Num_Exp("let application with diff body", 1, E);

  -- letrec F (X) = X in (F 1)
  E := new Expression'(Letrec_Exp, 'F', 'X',
         new Expression'(Var_Exp, 'X'),
         new Expression'(Call_Exp,
           new Expression'(Var_Exp, 'F'),
           new Expression'(Const_Exp, 1)));
  Test_Num_Exp("basic letrec (no recursion)", 1, E);

  -- if zero?(0) 2 5
  E := new Expression'(If_Exp,
         new Expression'(ZeroP_Exp, new Expression'(Const_Exp, 0)),
         new Expression'(Const_Exp, 2),
         new Expression'(Const_Exp, 5));
  Test_Num_Exp("basic if/zero? true", 2, E);

  -- if zero?(1) 2 5
  E := new Expression'(If_Exp,
         new Expression'(ZeroP_Exp, new Expression'(Const_Exp, 1)),
         new Expression'(Const_Exp, 2),
         new Expression'(Const_Exp, 5));
  Test_Num_Exp("basic if/zero? false", 5, E);

  -- letrec F (A) = if zero?(A) 0 (F -(A, 1)) in (F 3)
  E := new Expression'(Letrec_Exp, 'F', 'A',
         new Expression'(If_Exp,
           new Expression'(ZeroP_Exp, new Expression'(Var_Exp, 'A')),
           new Expression'(Const_Exp, 0),
           new Expression'(Call_Exp,
             new Expression'(Var_Exp, 'F'),
             new Expression'(Diff_Exp,
               new Expression'(Var_Exp, 'A'),
               new Expression'(Const_Exp, 1)))),
         new Expression'(Call_Exp,
           new Expression'(Var_Exp, 'F'),
           new Expression'(Const_Exp, 3)));
  Test_Num_Exp("recursive letrec app", 0, E);
end Run_Tests;
