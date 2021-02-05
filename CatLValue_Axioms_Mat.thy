section \<open>Quantum instantiation\<close>

theory CatLValue_Axioms_Mat
  imports Jordan_Normal_Form.Matrix_Impl
begin

class domain = enum

instance prod :: (domain,domain) domain ..

typedef (overloaded) ('a::enum) maps =
  \<open>carrier_mat CARD('a) CARD('a) :: complex mat set\<close>
  apply (rule exI[of _ \<open>zero_mat CARD('a) CARD('a)\<close>])
  by (auto simp: Let_def)
setup_lifting type_definition_maps

definition lvalueish where 
  \<open>lvalueish F \<longleftrightarrow> undefined F\<close>

typedef (overloaded) ('a,'b) lvalue = "{F::'a maps \<Rightarrow> 'b maps. lvalueish F}"
  morphisms lvalue_app Abs_lvalue
  sorry
setup_lifting type_definition_lvalue
notation lvalue_app (infixr "\<cdot>" 54)

definition is_lvalue_raw :: \<open>('a maps \<Rightarrow> 'b maps) \<Rightarrow> bool\<close> where
  "is_lvalue_raw F = undefined F"

definition "lvalues_exist = (\<lambda>(_::'a::domain itself) (_::'b::domain itself). 
  \<exists>(lv::'a maps \<Rightarrow> 'b maps). is_lvalue_raw lv)"

lift_definition maps_comp :: "('a::domain) maps \<Rightarrow> 'a maps \<Rightarrow> 'a maps" (infixl "o\<^sub>m" 55) is
  "times"
  sorry

lift_definition maps_tensor :: "'a::domain maps \<Rightarrow> 'b::domain maps \<Rightarrow> ('a\<times>'b) maps" (infixr "\<otimes>" 70) is
  undefined
  sorry

lift_definition lvalue_id :: "('a::domain,'a) lvalue" ("1\<^sub>l") is id
  sorry

lift_definition is_lvalue :: \<open>('a::domain, 'b::domain) lvalue \<Rightarrow> bool\<close> is
  \<open>\<lambda>F. undefined F\<close>.

lemma lvalues_exist_comp:
  assumes "lvalues_exist TYPE('b::domain) TYPE('c::domain)"
  assumes "lvalues_exist TYPE('a::domain) TYPE('b::domain)"
  shows "lvalues_exist TYPE('a::domain) TYPE('c::domain)"
  sorry

definition "some_lvalue = (SOME lv. is_lvalue_raw lv)"

lemma some_lvalue_is_lvalue: "lvalues_exist TYPE('a::domain) TYPE('b::domain) \<Longrightarrow>
  is_lvalue_raw (some_lvalue :: 'a maps \<Rightarrow> 'b maps)"
  by (metis lvalues_exist_def someI some_lvalue_def)

lift_definition lvalue_comp :: "('b::domain,'c::domain) lvalue 
               \<Rightarrow> ('a::domain,'b) lvalue \<Rightarrow> ('a,'c) lvalue" (infixl "o\<^sub>l" 55)
  is comp
  unfolding lvalueish_def sorry

lemma
  comp_is_lvalue: "is_lvalue x \<Longrightarrow> is_lvalue y \<Longrightarrow> is_lvalue (x o\<^sub>l y)"
  sorry

lift_definition lvalue_tensor :: 
  "('a::domain,'c::domain) lvalue \<Rightarrow> ('b::domain,'d::domain) lvalue 
        \<Rightarrow> ('a\<times>'b,'c\<times>'d) lvalue" is
  "\<lambda>x y f. undefined"
  sorry

lemma lvalue_id: "1\<^sub>l \<cdot> x = x"
  by (transfer, simp)

lemma lvalue_comp_app: 
  fixes y :: "('a::domain,'b::domain) lvalue" and x :: "('b,'c::domain) lvalue"
  (* assumes "lvalues_exist TYPE('a) TYPE('b)" *)
  (* assumes "lvalues_exist TYPE('b) TYPE('c)" *)
  shows "(x o\<^sub>l y) \<cdot> f = x \<cdot> y \<cdot> f"
  apply transfer by auto
  
lemma lvalue_app_mult: 
  fixes x :: "('a::domain,'b::domain) lvalue"
  assumes "is_lvalue x"
  shows "x \<cdot> (f o\<^sub>m g) = (x \<cdot> f) o\<^sub>m (x \<cdot> g)"
  using assms apply transfer unfolding is_lvalue_raw_def 
  sorry

lemma maps_comp_assoc: "(f o\<^sub>m g) o\<^sub>m h = f o\<^sub>m (g o\<^sub>m h)"
  apply transfer by simp

(* lemma lvalue_tensor_app[simp]: "(lvalue_tensor x y) \<cdot> (f \<otimes> g) = (x \<cdot> f) \<otimes> (y \<cdot> g)"
  apply transfer 
  by - *)

lemma tensor_extensionality:
  fixes x y :: "('a::domain\<times>'b::domain, 'c::domain) lvalue"
  shows "(\<And>f g. x \<cdot> (f \<otimes> g) = y \<cdot> (f \<otimes> g)) \<Longrightarrow> x = y"
  sorry

lift_definition pair :: "('a::domain, 'c::domain) lvalue \<Rightarrow> ('b::domain, 'c) lvalue \<Rightarrow> ('a \<times> 'b, 'c) lvalue" is
  "\<lambda>x y. undefined"
  sorry

lemma pair_apply: \<open>pair x y \<cdot> (f \<otimes> g) = (x \<cdot> f) o\<^sub>m (y \<cdot> g)\<close>
  sorry

(* lemma pair_apply0: 
  assumes "\<And>f g. (x \<cdot> f) o\<^sub>m (y \<cdot> g) = (y \<cdot> g) o\<^sub>m (x \<cdot> f)"
  shows "pair x y \<cdot> (f \<otimes> g) = (x \<cdot> f) o\<^sub>m (y \<cdot> g)"
  apply transfer
  sorry *)

lemma
  pair_is_lvalue0: 
  \<open>\<lbrakk>is_lvalue x; is_lvalue y;
    \<And>f g. (x \<cdot> f) o\<^sub>m (y \<cdot> g) = (y \<cdot> g) o\<^sub>m (x \<cdot> f)\<rbrakk>
     \<Longrightarrow> is_lvalue (pair x y)\<close>
  sorry

lift_definition left_tensor :: "'a::domain maps \<Rightarrow> ('b::domain, 'a \<times> 'b) lvalue" is
  "\<lambda>f g. f \<otimes> g"
  sorry

lemma left_tensor_apply: "left_tensor f \<cdot> g = f \<otimes> g"
  apply (transfer fixing: f g) by simp

lift_definition swap :: "('a\<times>'b, 'b\<times>'a) lvalue" is
  "\<lambda>f. undefined" 
  sorry

lemma swap_apply[simp]: "swap \<cdot> (f \<otimes> g) = g \<otimes> f"
  sorry

lift_definition assoc :: "('a \<times> ('b \<times> 'c), ('a \<times> 'b) \<times> 'c) lvalue" is
  "undefined"
  sorry

lemma assoc_apply[simp]: "assoc \<cdot> (f \<otimes> (g \<otimes> h)) = (f \<otimes> g) \<otimes> h"
  sorry

lift_definition assoc' :: "(('a \<times> 'b) \<times> 'c, 'a \<times> ('b \<times> 'c)) lvalue" is
  undefined
  sorry

lemma assoc'_apply[simp]: "assoc' \<cdot> (f \<otimes> g) \<otimes> h = (f \<otimes> (g \<otimes> h))"
  sorry

end
