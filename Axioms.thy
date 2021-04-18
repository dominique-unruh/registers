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

axiomatization update_hom :: \<open>('a::domain update \<Rightarrow> 'b::domain update) \<Rightarrow> bool\<close>
axiomatization where
  comp_update_hom: "update_hom F \<Longrightarrow> update_hom G \<Longrightarrow> update_hom (G \<circ> F)" and
  id_update_hom: \<open>update_hom id\<close>
for F :: \<open>'a::domain update \<Rightarrow> 'b::domain update\<close> and G :: \<open>'b update \<Rightarrow> 'c::domain update\<close>

axiomatization where
  update_hom_mult_right: \<open>update_hom (\<lambda>a. comp_update a z)\<close> and
  update_hom_mult_left: \<open>update_hom (\<lambda>a. comp_update z a)\<close>
    for z :: "'a::domain update"

axiomatization tensor_update :: \<open>'a::domain update \<Rightarrow> 'b::domain update \<Rightarrow> ('a\<times>'b) update\<close> 
    where tensor_extensionality: "update_hom F \<Longrightarrow> update_hom G \<Longrightarrow> (\<And>a b. F (tensor_update a b) = G (tensor_update a b)) \<Longrightarrow> F = G"
    for F G :: \<open>('a\<times>'b) update \<Rightarrow> 'c::domain update\<close>

axiomatization where tensor_update_mult: \<open>comp_update (tensor_update a c) (tensor_update b d) = tensor_update (comp_update a b) (comp_update c d)\<close>
  for a b :: \<open>'a::domain update\<close> and c d :: \<open>'b::domain update\<close>


axiomatization where
  update_hom_tensor_left_is_hom: "update_hom (tensor_update a :: 'b::domain update \<Rightarrow> _)" and
  update_hom_tensor_right_is_hom: "update_hom (\<lambda>a::'a::domain update. tensor_update a b)"
  for a :: "'a::domain update" and b :: "'b::domain update"

axiomatization lvalue :: \<open>('a update \<Rightarrow> 'b update) \<Rightarrow> bool\<close>
axiomatization where
  lvalue_hom: "lvalue F \<Longrightarrow> update_hom F" and
  lvalue_comp: "lvalue F \<Longrightarrow> lvalue G \<Longrightarrow> lvalue (G \<circ> F)"  and
  lvalue_mult: "lvalue F \<Longrightarrow> comp_update (F a) (F b) = F (comp_update a b)" and
  lvalue_of_id: \<open>lvalue F \<Longrightarrow> F id_update = id_update\<close>
for F :: "'a::domain update \<Rightarrow> 'b::domain update" and G :: "'b update \<Rightarrow> 'c::domain update" 

axiomatization where lvalue_tensor_left: \<open>lvalue (\<lambda>a. tensor_update a id_update)\<close>
axiomatization where lvalue_tensor_right: \<open>lvalue (\<lambda>a. tensor_update id_update a)\<close>

axiomatization lvalue_pair ::
  \<open>('a::domain update \<Rightarrow> 'c::domain update) \<Rightarrow> ('b::domain update \<Rightarrow> 'c update)
         \<Rightarrow> (('a\<times>'b) update \<Rightarrow> 'c update)\<close> where
  lvalue_pair_lvalue: \<open>lvalue F \<Longrightarrow> lvalue G \<Longrightarrow> (\<And>a b. comp_update (F a) (G b) = comp_update (G b) (F a))
       \<Longrightarrow> lvalue (lvalue_pair F G)\<close> and
  lvalue_pair_apply: \<open>lvalue F \<Longrightarrow> lvalue G \<Longrightarrow> (\<And>a b. comp_update (F a) (G b) = comp_update (G b) (F a))
       \<Longrightarrow> (lvalue_pair F G) (tensor_update a b) = comp_update (F a) (G b)\<close>

end
