theory CatLValue_Syntax
  imports CatLValue
begin


nonterminal lvalue_expr
nonterminal lvalue_expr_chain
nonterminal lvalue_expr_atom

syntax "" :: "id \<Rightarrow> lvalue_expr_atom" ("_")
syntax "" :: "lvalue_expr \<Rightarrow> lvalue_expr_atom" ("'(_')")

(* syntax "" :: "lvalue_expr_atom \<Rightarrow> lvalue_expr_indexed" ("_") *)
(* syntax "lvalue_index" :: "lvalue_expr_atom \<Rightarrow> 'a \<Rightarrow> lvalue_expr_indexed" ("_[_]") *)

syntax "" :: "lvalue_expr_atom \<Rightarrow> lvalue_expr_chain" ("_")
syntax "_lvalue_index" :: "lvalue_expr_chain \<Rightarrow> 'a \<Rightarrow> lvalue_expr_chain" ("_[_]")
syntax "chain" :: "lvalue_expr_chain \<Rightarrow> lvalue_expr_atom \<Rightarrow> lvalue_expr_chain" (infixl "\<rightarrow>" 90)

syntax "" :: "lvalue_expr_chain \<Rightarrow> lvalue_expr" ("_")
syntax "pair" :: "lvalue_expr_chain \<Rightarrow> lvalue_expr \<Rightarrow> lvalue_expr" (infixr "," 80)
syntax "_lvalue_expr" :: "lvalue_expr \<Rightarrow> 'a" ("\<lbrakk>_\<rbrakk>")

(* translations "_lvalue_id x" \<rightharpoonup> "x" *)
(* translations "_lvalue_paren x" \<rightharpoonup> "x" *)
(* translations "_lvalue_pair x y" \<rightharpoonup> "CONST lvalue_pair x y" *)
(* translations "_lvalue_index x i" \<rightharpoonup> "CONST chain x (CONST function_lvalue i)" *)
translations "_lvalue_expr x" \<rightharpoonup> "x :: (_,_) lvalue"
(* translations "_lvalue_chain x y" \<rightharpoonup> "CONST lvalue_chain x y" *)

(* term "\<lbrakk>x[3]\<rbrakk>" *)
term "\<lbrakk>x\<rightarrow>fst_lvalue, y\<rbrakk>"
term "\<lbrakk>(x,z)\<rightarrow>x, y\<rbrakk>"



end
