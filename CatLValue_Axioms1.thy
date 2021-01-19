theory CatLValue_Axioms1
imports Main
begin

axiomatization domain_ax :: "'a itself \<Rightarrow> bool"
axiomatization where
  domain_axI: "domain_ax TYPE('a) \<Longrightarrow> domain_ax TYPE('b) \<Longrightarrow> domain_ax TYPE('a\<times>'b)"
class domain = assumes domain_ax: "domain_ax TYPE('a)"

instance prod :: (domain,domain) domain 
  apply intro_classes apply (rule domain_axI) using domain_ax by auto

hide_fact domain_ax domain_axI
hide_const domain_ax

typedecl 'a maps
typedecl ('a,'c) lvalue

axiomatization 
  maps_comp :: "('a::domain) maps \<Rightarrow> 'a maps \<Rightarrow> 'a maps" (infixl "o\<^sub>m" 55) and
  maps_tensor :: "'a maps \<Rightarrow> 'b::domain maps \<Rightarrow> ('a\<times>'b) maps" (infixr "\<otimes>" 70) and
  lvalue_app :: "('a, 'b) lvalue \<Rightarrow> 
                  'a maps \<Rightarrow> 'b maps" (infixr "\<cdot>" 54) and
  lvalue_comp :: "('b,'c::domain) lvalue 
               \<Rightarrow> ('a,'b) lvalue \<Rightarrow> ('a,'c) lvalue" (infixl "o\<^sub>l" 55)

axiomatization where
  lvalue_comp_app[simp]: "(x o\<^sub>l y) \<cdot> f = x \<cdot> y \<cdot> f"
axiomatization where
  lvalue_app_mult: "x \<cdot> (f o\<^sub>m g) = (x \<cdot> f) o\<^sub>m (x \<cdot> g)"
axiomatization where
  maps_comp_assoc: "(f o\<^sub>m g) o\<^sub>m h = f o\<^sub>m (g o\<^sub>m h)"

axiomatization where tensor_extensionality:
  "(\<And>f g. x \<cdot> (f \<otimes> g) = y \<cdot> (f \<otimes> g)) \<Longrightarrow> x = y"

axiomatization where
  pair_exists: \<open>\<exists>xy. (\<forall>f g. xy \<cdot> (f \<otimes> g) = (x \<cdot> f) o\<^sub>m (y \<cdot> g))\<close>

axiomatization left_tensor where
  left_tensor_apply[simp]: "left_tensor f \<cdot> g = f \<otimes> g"

axiomatization swap where
  swap_apply[simp]: "swap \<cdot> (f \<otimes> g) = g \<otimes> f"

end
