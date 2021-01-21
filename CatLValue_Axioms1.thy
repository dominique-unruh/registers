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
  lvalue_id :: "('a,'a) lvalue" ("1\<^sub>l") and
  lvalue_app :: "('a, 'b) lvalue \<Rightarrow> 
                  'a maps \<Rightarrow> 'b maps" (infixr "\<cdot>" 54) and
  lvalue_comp :: "('b,'c::domain) lvalue 
               \<Rightarrow> ('a,'b) lvalue \<Rightarrow> ('a,'c) lvalue" (infixl "o\<^sub>l" 55) and
  lvalue_tensor :: "('a,'c) lvalue \<Rightarrow> ('e,'g::domain) lvalue \<Rightarrow> ('a\<times>'e,'c\<times>'g) lvalue"

axiomatization where
  lvalue_id[simp]: "1\<^sub>l \<cdot> x = x"
axiomatization where
  lvalue_comp_app[simp]: "(x o\<^sub>l y) \<cdot> f = x \<cdot> y \<cdot> f"
axiomatization where
  lvalue_app_mult: "x \<cdot> (f o\<^sub>m g) = (x \<cdot> f) o\<^sub>m (x \<cdot> g)"
axiomatization where
  maps_comp_assoc: "(f o\<^sub>m g) o\<^sub>m h = f o\<^sub>m (g o\<^sub>m h)"
axiomatization where
  lvalue_tensor_app[simp]: "(lvalue_tensor x y) \<cdot> (f \<otimes> g) = (x \<cdot> f) \<otimes> (y \<cdot> g)"

axiomatization where tensor_extensionality:
  "(\<And>f g. x \<cdot> (f \<otimes> g) = y \<cdot> (f \<otimes> g)) \<Longrightarrow> x = y"

axiomatization pair where
  pair_apply0: \<open>
    (\<And>f g. (x \<cdot> f) o\<^sub>m (y \<cdot> g) = (y \<cdot> g) o\<^sub>m (x \<cdot> f)) \<Longrightarrow>
    pair x y \<cdot> (f \<otimes> g) = (x \<cdot> f) o\<^sub>m (y \<cdot> g)\<close>

axiomatization where compatible30:
\<open>\<lbrakk>\<And>f g. (x \<cdot> f) o\<^sub>m (y \<cdot> g) = (y \<cdot> g) o\<^sub>m (x \<cdot> f);
  \<And>f h. (x \<cdot> f) o\<^sub>m (z \<cdot> h) = (z \<cdot> h) o\<^sub>m (x \<cdot> f);
  \<And>g h. (y \<cdot> g) o\<^sub>m (z \<cdot> h) = (z \<cdot> h) o\<^sub>m (y \<cdot> g)\<rbrakk>
    \<Longrightarrow> (pair x y \<cdot> fg) o\<^sub>m (z \<cdot> h) = (z \<cdot> h) o\<^sub>m (pair x y \<cdot> fg)\<close>

axiomatization left_tensor where
  left_tensor_apply[simp]: "left_tensor f \<cdot> g = f \<otimes> g"

axiomatization swap where
  swap_apply[simp]: "swap \<cdot> (f \<otimes> g) = g \<otimes> f"

axiomatization assoc where
  assoc_apply[simp]: "assoc \<cdot> (f \<otimes> (g \<otimes> h)) = (f \<otimes> g) \<otimes> h"

axiomatization assoc' where
  assoc'_apply[simp]: "assoc' \<cdot> (f \<otimes> g) \<otimes> h = (f \<otimes> (g \<otimes> h))"

end
