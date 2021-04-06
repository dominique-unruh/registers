section \<open>Axioms of lvalues\<close>

theory Axioms
  imports Main
begin

class domain
instance prod :: (domain,domain) domain
  by intro_classes

typedecl 'a update
axiomatization comp_update :: "'a::domain update \<Rightarrow> 'a update \<Rightarrow> 'a update" where
  comp_update_assoc: "comp_update (comp_update a b) c = comp_update a (comp_update b c)"
axiomatization id_update :: "'a::domain update" where
  id_update_left: "comp_update id_update a = a" and
  id_update_right: "comp_update a id_update = a"

type_synonym ('a,'b) update_hom = \<open>'a update \<Rightarrow> 'b update\<close>
axiomatization update_hom :: \<open>('a::domain,'b::domain) update_hom \<Rightarrow> bool\<close>
axiomatization where
  comp_update_hom: "update_hom F \<Longrightarrow> update_hom G \<Longrightarrow> update_hom (G \<circ> F)" and
  id_update_hom: \<open>update_hom id\<close>
for F :: \<open>('a::domain, 'b::domain) update_hom\<close> and G :: \<open>('b, 'c::domain) update_hom\<close>

type_synonym ('a,'b,'c) update_2hom = \<open>'a update \<Rightarrow> 'b update \<Rightarrow> 'c update\<close>

axiomatization update_2hom :: "('a::domain, 'b::domain, 'c::domain) update_2hom \<Rightarrow> bool"
axiomatization where update_hom_o_2hom_is_2hom: \<open>update_2hom F2 \<Longrightarrow> update_hom G \<Longrightarrow> update_2hom (\<lambda>a b. G (F2 a b))\<close>
  for F2 :: \<open>('a::domain, 'b::domain, 'c::domain) update_2hom\<close> and G :: \<open>('c, 'd::domain) update_hom\<close>
axiomatization where update_2hom_o_hom_left_is_hom: \<open>update_2hom F2 \<Longrightarrow> update_hom G \<Longrightarrow> update_2hom (\<lambda>a b. F2 (G a) b)\<close>
  for F2 :: \<open>('a::domain, 'b::domain, 'c::domain) update_2hom\<close> and G :: \<open>('d::domain, 'a) update_hom\<close>
axiomatization where update_2hom_sym: \<open>update_2hom F2 \<Longrightarrow> update_2hom (\<lambda>a b. F2 b a)\<close>
  for F2 :: \<open>('a::domain, 'b::domain, 'c::domain) update_2hom\<close>
axiomatization where update_2hom_left_is_hom: \<open>update_2hom F2 \<Longrightarrow> update_hom (\<lambda>a. F2 a b)\<close>
  for F2 :: \<open>('a::domain, 'b::domain, 'c::domain) update_2hom\<close>

axiomatization where comp_update_is_2hom: "update_2hom comp_update"

axiomatization tensor_lift :: \<open>('a::domain, 'b::domain, 'c::domain) update_2hom
                            \<Rightarrow> (('a\<times>'b, 'c) update_hom)\<close>
    and tensor_update :: \<open>'a update \<Rightarrow> 'b update \<Rightarrow> ('a\<times>'b) update\<close> 
    where tensor_update_is_2hom: \<open>update_2hom tensor_update\<close>
      and tensor_lift_hom: "update_2hom F2 \<Longrightarrow> update_hom (tensor_lift F2)"
      and tensor_lift_correct:  \<open>update_2hom F2 \<Longrightarrow> (\<lambda>a b. tensor_lift F2 (tensor_update a b)) = F2\<close>
      and tensor_extensionality: "update_hom F \<Longrightarrow> update_hom G \<Longrightarrow> (\<And>a b. F (tensor_update a b) = G (tensor_update a b)) \<Longrightarrow> F = G"
    for F2 :: \<open>('a::domain, 'b::domain, 'c::domain) update_2hom\<close>
      and F G :: \<open>('a\<times>'b, 'c) update_hom\<close>

axiomatization where tensor_update_mult: \<open>comp_update (tensor_update a c) (tensor_update b d) = tensor_update (comp_update a b) (comp_update c d)\<close>
  for a b :: \<open>'a::domain update\<close> and c d :: \<open>'b::domain update\<close>

axiomatization lvalue :: \<open>('a,'b) update_hom \<Rightarrow> bool\<close>
axiomatization where
  lvalue_hom: "lvalue F \<Longrightarrow> update_hom F" and
  lvalue_comp: "lvalue F \<Longrightarrow> lvalue G \<Longrightarrow> lvalue (G \<circ> F)"  and
  lvalue_mult: "lvalue F \<Longrightarrow> comp_update (F a) (F b) = F (comp_update a b)" and
  lvalue_of_id: \<open>lvalue F \<Longrightarrow> F id_update = id_update\<close>
for F :: "('a::domain,'b::domain) update_hom" and G :: "('b,'c::domain) update_hom" 

axiomatization where lvalue_tensor_left: \<open>lvalue (\<lambda>a. tensor_update a id_update)\<close>
axiomatization where lvalue_tensor_right: \<open>lvalue (\<lambda>a. tensor_update id_update a)\<close>

axiomatization where
  pair_lvalue_axiom: \<open>\<lbrakk>lvalue F; lvalue G; update_hom p;
    \<And>a b. comp_update (F a) (G b) = comp_update (G b) (F a);
    \<And>a b. p (tensor_update a b) = comp_update (F a) (G b)\<rbrakk> \<Longrightarrow> lvalue p\<close>
for F :: \<open>('a::domain, 'c::domain) update_hom\<close> and G :: \<open>('b::domain, 'c::domain) update_hom\<close>

end
