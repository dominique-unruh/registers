theory CatLValue_Axioms_Fun
  imports Main
begin

class domain

instance prod :: (domain,domain) domain ..

type_synonym 'a maps = "'a\<Rightarrow>'a"

definition is_lvalue :: "('a::domain \<Rightarrow> 'b::domain maps) \<times> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
  "is_lvalue = (\<lambda>(upd, get). 
     (\<forall>f g m. upd f (upd g m) = upd f m) \<and>
     (\<forall>f m. get (upd f m) = f) \<and>
     (\<forall>m. upd (get m) m = m))"

lemma is_lvalueI:
  assumes "\<And>a b m. upd a (upd b m) = upd a m"
  assumes "\<And>a m. get (upd a m) = a"
  assumes "\<And>m. upd (get m) m = m"
  shows "is_lvalue (upd, get)"
  using assms by (auto simp: is_lvalue_def)

lemma lvalue_upd_upd: "is_lvalue (upd, get) \<Longrightarrow> upd f (upd g m) = upd f m"
  by (auto simp: is_lvalue_def o_def)

lemma lvalue_get_upd: "is_lvalue (upd, get) \<Longrightarrow> get (upd f m) = f"
  by (simp add: is_lvalue_def)

lemma lvalue_upd_get: "is_lvalue (upd, get) \<Longrightarrow> upd (get m) m = m"
  by (auto simp: is_lvalue_def)

definition "lvalues_exist = (\<lambda>(_::'a::domain itself) (_::'b::domain itself). 
  \<exists>(lv::_ \<times> ('b\<Rightarrow>'a)). is_lvalue lv)"

typedef ('a,'b) lvalue = "{(f::'a::domain \<Rightarrow> 'b::domain maps, g::'b \<Rightarrow> 'a). 
  lvalues_exist TYPE('a) TYPE('b) \<longrightarrow> is_lvalue (f,g)}"
  unfolding lvalues_exist_def by auto
setup_lifting type_definition_lvalue

abbreviation (input) maps_comp :: "('a::domain) maps \<Rightarrow> 'a maps \<Rightarrow> 'a maps" (infixl "o\<^sub>m" 55)
  where "maps_comp == comp"

abbreviation (input) maps_tensor :: "'a maps \<Rightarrow> 'b::domain maps \<Rightarrow> ('a\<times>'b) maps" (infixr "\<otimes>" 70) 
  where "maps_tensor == map_prod"

lift_definition lvalue_id :: "('a::domain,'a) lvalue" ("1\<^sub>l") is "(\<lambda>f _. f, id)"
  unfolding is_lvalue_def by auto

lift_definition lvalue_app :: "('a::domain, 'b::domain) lvalue \<Rightarrow> 'a maps \<Rightarrow> 'b maps" (infixr "\<cdot>" 54) 
  is "\<lambda>(s,g) f m. s (f (g m)) m".

lift_definition lvalue_setter :: "('a::domain, 'b::domain) lvalue \<Rightarrow> 'a \<Rightarrow> 'b maps"
  is fst.

lift_definition lvalue_getter :: "('a::domain, 'b::domain) lvalue \<Rightarrow> 'b \<Rightarrow> 'a"
  is snd.

lemma is_lvalue_comp:
  assumes "is_lvalue (upd1, get1)"
  assumes "is_lvalue (upd2, get2)"
  shows "is_lvalue (\<lambda>c m. upd1 (upd2 c (get1 m)) m, get2 o get1)"
proof (rule is_lvalueI)
  fix a b m
  show \<open>upd1 (upd2 a (get1 (upd1 (upd2 b (get1 m)) m))) (upd1 (upd2 b (get1 m)) m) =
       upd1 (upd2 a (get1 m)) m\<close>
    by (metis (mono_tags, lifting) assms(1) assms(2) lvalue_get_upd lvalue_upd_upd)
  show \<open>(get2 \<circ> get1) (upd1 (upd2 a (get1 m)) m) = a\<close>
    by (simp add: assms(1) assms(2) lvalue_get_upd)
  show \<open>upd1 (upd2 ((get2 \<circ> get1) m) (get1 m)) m = m\<close>
    by (simp add: assms(1) assms(2) lvalue_upd_get)
qed

lemma lvalues_exist_comp:
  assumes "lvalues_exist TYPE('b::domain) TYPE('c::domain)"
  assumes "lvalues_exist TYPE('a::domain) TYPE('b::domain)"
  shows "lvalues_exist TYPE('a::domain) TYPE('c::domain)"
  using assms unfolding lvalues_exist_def
  using is_lvalue_comp apply auto by blast

definition "some_lvalue = (SOME lv. is_lvalue lv)"

lemma some_lvalue_is_lvalue: "lvalues_exist TYPE('a::domain) TYPE('b::domain) \<Longrightarrow>
  is_lvalue (some_lvalue :: _ \<times> ('b\<Rightarrow>'a))"
  by (metis lvalues_exist_def someI some_lvalue_def)

lift_definition lvalue_comp :: "('b::domain,'c::domain) lvalue 
               \<Rightarrow> ('a::domain,'b) lvalue \<Rightarrow> ('a,'c) lvalue" (infixl "o\<^sub>l" 55) 
  is \<open>if lvalues_exist TYPE('b) TYPE('c) \<and> lvalues_exist TYPE('a) TYPE('b)
      then (\<lambda>(upd1,get1) (upd2,get2). (\<lambda>c m. upd1 (upd2 c (get1 m)) m, get2 o get1))
      else (\<lambda>_ _. some_lvalue)\<close>
  apply (cases \<open>lvalues_exist TYPE('b) TYPE('c) \<and> lvalues_exist TYPE('a) TYPE('b)\<close>)
  by (auto intro!: some_lvalue_is_lvalue simp add: is_lvalue_comp)

(* lift_definition lvalue_tensor :: 
  "('a::domain,'c::domain) lvalue \<Rightarrow> ('b::domain,'d::domain) lvalue 
        \<Rightarrow> ('a\<times>'b,'c\<times>'d) lvalue" is
  "\<lambda>x y f. undefined"
  by - *)

lemma lvalue_id[simp]: "1\<^sub>l \<cdot> x = x"
  by (transfer, simp)

lemma lvalue_comp_app[simp]: 
  fixes y :: "('a::domain,'b::domain) lvalue" and x :: "('b,'c::domain) lvalue"
  assumes "lvalues_exist TYPE('a) TYPE('b)"
  assumes "lvalues_exist TYPE('b) TYPE('c)"
  shows "(x o\<^sub>l y) \<cdot> f = x \<cdot> y \<cdot> f"
  using assms apply transfer by auto
  
lemma lvalue_app_mult: 
  fixes x :: "('a::domain,'b::domain) lvalue"
  assumes "lvalues_exist TYPE('a) TYPE('b)"
  shows "x \<cdot> (f o\<^sub>m g) = (x \<cdot> f) o\<^sub>m (x \<cdot> g)"
  using assms apply transfer unfolding is_lvalue_def by auto

lemma maps_comp_assoc: "(f o\<^sub>m g) o\<^sub>m h = f o\<^sub>m (g o\<^sub>m h)"
  by auto

(* lemma lvalue_tensor_app[simp]: "(lvalue_tensor x y) \<cdot> (f \<otimes> g) = (x \<cdot> f) \<otimes> (y \<cdot> g)"
  apply transfer 
  by - *)

lemma tensor_extensionality:
  fixes x y :: "('a::domain\<times>'b::domain, 'c::domain) lvalue"
  assumes "lvalues_exist TYPE('a\<times>'b) TYPE('c)"
  shows "(\<And>f g. x \<cdot> (f \<otimes> g) = y \<cdot> (f \<otimes> g)) \<Longrightarrow> x = y"
  apply transfer unfolding is_lvalue_def
    apply (auto simp: assms o_def map_prod_def)
  sorry

lift_definition pair :: "('a::domain, 'c::domain) lvalue \<Rightarrow> ('b::domain, 'c) lvalue \<Rightarrow> ('a \<times> 'b, 'c) lvalue" is
  "\<lambda>x y. undefined"
  sorry

lemma pair_apply0: 
  assumes "\<And>f g. (x \<cdot> f) o\<^sub>m (y \<cdot> g) = (y \<cdot> g) o\<^sub>m (x \<cdot> f)"
  shows "pair x y \<cdot> (f \<otimes> g) = (x \<cdot> f) o\<^sub>m (y \<cdot> g)"
  apply transfer
  sorry

(* TODO: cannot define left_tensor: left_tensor f \<cdot> 1 \<noteq> 1 \<Longrightarrow> not a functor *)
lift_definition left_tensor :: "('a::domain \<Rightarrow> 'a) \<Rightarrow> ('b::domain, 'a \<times> 'b) lvalue" is
  "\<lambda>f. (undefined, undefined)"

lemma left_tensor_apply[simp]: "left_tensor f \<cdot> g = f \<otimes> g"
  apply transfer by simp

lift_definition swap :: "('a\<times>'b, 'b\<times>'a) lvalue" is
  "\<lambda>f. prod.swap o f o prod.swap" ..

lemma swap_apply[simp]: "swap \<cdot> (f \<otimes> g) = g \<otimes> f"
  by (transfer, auto)

lift_definition assoc :: "('a \<times> ('b \<times> 'c), ('a \<times> 'b) \<times> 'c) lvalue" is
  "\<lambda>f. (\<lambda>(a,(b,c)). ((a,b),c)) o f o (\<lambda>((a,b),c). (a,(b,c)))"
  ..

lemma assoc_apply[simp]: "assoc \<cdot> (f \<otimes> (g \<otimes> h)) = (f \<otimes> g) \<otimes> h"
  by (transfer, auto)

lift_definition assoc' :: "(('a \<times> 'b) \<times> 'c, 'a \<times> ('b \<times> 'c)) lvalue" is
  "\<lambda>f. (\<lambda>((a,b),c). (a,(b,c))) o f o (\<lambda>(a,(b,c)). ((a,b),c))"
  ..

lemma assoc'_apply[simp]: "assoc' \<cdot> (f \<otimes> g) \<otimes> h = (f \<otimes> (g \<otimes> h))"
  by (transfer, auto)

end
