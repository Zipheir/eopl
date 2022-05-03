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
begin
  E := new Expression'(Diff_Exp,
           new Expression'(Const_Exp, 5),
           new Expression'(Const_Exp, 2));
  Test_Num_Exp("diff constants", 3, E);
end Run_Tests;
