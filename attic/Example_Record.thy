theory Example_Record
  imports LValues_Typed
begin

record state =
  x :: "nat list"
  y :: nat
  z :: string

print_theorems

abbreviation "x_var == mk_lvalue x (\<lambda>a m. m\<lparr>x:=a\<rparr>)"
abbreviation "y_var == mk_lvalue y (\<lambda>a m. m\<lparr>y:=a\<rparr>)"
abbreviation "z_var == mk_lvalue z (\<lambda>a m. m\<lparr>z:=a\<rparr>)"

lemma [simp]: "valid_lvalue x_var"
  apply (rule mk_lvalue_valid) by auto
lemma [simp]: "valid_lvalue y_var"
  apply (rule mk_lvalue_valid) by auto
lemma [simp]: "valid_lvalue z_var"
  apply (rule mk_lvalue_valid) by auto

lemma [simp]: "compatible_lvalues x_var y_var"
  apply (rule mk_lvalue_compat) by auto

lemma [simp]: "compatible_lvalues x_var z_var"
  apply (rule mk_lvalue_compat) by auto

lemma [simp]: "compatible_lvalues y_var z_var"
  apply (rule mk_lvalue_compat) by auto

lemma [simp]: "compatible_lvalues y_var x_var"
  apply (rule mk_lvalue_compat) by auto

lemma [simp]: "compatible_lvalues z_var x_var"
  apply (rule mk_lvalue_compat) by auto

lemma [simp]: "compatible_lvalues z_var y_var"
  apply (rule mk_lvalue_compat) by auto

lemma "setter (lvalue_pair z_var x_var) (''hello'', [4]) \<lparr>x=[], y=4, z=''abc''\<rparr> = 
          \<lparr>x = [4], y = 4, z = ''hello''\<rparr>"
  by simp

end
