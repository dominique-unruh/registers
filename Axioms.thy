theory Axioms
  imports Main
begin

class domain
instance prod :: (domain,domain) domain
  by intro_classes

typedecl 'a domain_end
axiomatization comp_domain :: "'a::domain domain_end \<Rightarrow> 'a domain_end \<Rightarrow> 'a domain_end" where
  comp_domain_assoc: "comp_domain (comp_domain a b) c = comp_domain a (comp_domain b c)"
(* TODO: category laws *)

type_synonym ('a,'b) maps_hom = \<open>'a domain_end \<Rightarrow> 'b domain_end\<close>
axiomatization maps_hom :: \<open>('a::domain,'b::domain) maps_hom \<Rightarrow> bool\<close>
axiomatization where
  comp_maps_hom: "maps_hom F \<Longrightarrow> maps_hom G \<Longrightarrow> maps_hom (G \<circ> F)"
(* TODO category laws *)

type_synonym ('a,'b,'c) maps_2hom = \<open>'a domain_end \<Rightarrow> 'b domain_end \<Rightarrow> 'c domain_end\<close>

(* TODO: Update notes PDF accordingly *)
(* definition maps_2hom :: "('a::domain, 'b::domain, 'c::domain) maps_2hom \<Rightarrow> bool" where
  "maps_2hom F \<longleftrightarrow> (\<forall>a. maps_hom (F a)) \<and> (\<forall>b. maps_hom (\<lambda>a. F a b))" *)
axiomatization maps_2hom :: "('a::domain, 'b::domain, 'c::domain) maps_2hom \<Rightarrow> bool"
axiomatization where maps_hom_2hom_comp: \<open>maps_2hom F2 \<Longrightarrow> maps_hom G \<Longrightarrow> maps_2hom (\<lambda>a b. G (F2 a b))\<close>
axiomatization where maps_2hom_hom_comp1: \<open>maps_2hom F2 \<Longrightarrow> maps_hom G \<Longrightarrow> maps_2hom (\<lambda>a b. F2 (G a) b)\<close>
(* axiomatization where maps_2hom_hom_comp2: \<open>maps_2hom F2 \<Longrightarrow> maps_hom G \<Longrightarrow> maps_2hom (\<lambda>a b. F2 a (G b))\<close>  *)
axiomatization where maps_2hom_sym: \<open>maps_2hom F2 \<Longrightarrow> maps_2hom (\<lambda>a b. F2 b a)\<close> 
axiomatization where maps_2hom_left: \<open>maps_2hom F2 \<Longrightarrow> maps_hom (\<lambda>a. F2 a b)\<close>
(* axiomatization where maps_2hom_right: \<open>maps_2hom F2 \<Longrightarrow> maps_hom (\<lambda>b. F2 a b)\<close> *)




axiomatization where comp_2hom: "maps_2hom comp_domain"

(* Tensor product on Maps *)
axiomatization tensor_lift :: \<open>('a::domain, 'b::domain, 'c::domain) maps_2hom
                            \<Rightarrow> (('a\<times>'b, 'c) maps_hom)\<close>
    and tensor_maps :: \<open>'a domain_end \<Rightarrow> 'b domain_end \<Rightarrow> ('a\<times>'b) domain_end\<close>
    where
  tensor_2hom: \<open>maps_2hom tensor_maps\<close> and
  tensor_lift_hom: "maps_2hom F2 \<Longrightarrow> maps_hom (tensor_lift F2)" and
  tensor_existence:  \<open>maps_2hom F2 \<Longrightarrow> (\<lambda>a b. tensor_lift F2 (tensor_maps a b)) = F2\<close> and
  tensor_uniqueness: \<open>maps_2hom F2 \<Longrightarrow> maps_hom F \<Longrightarrow> (\<lambda>a b. F (tensor_maps a b)) = F2 \<Longrightarrow> F = tensor_lift F2\<close>
(* Formalize the weak property instead *)

axiomatization assoc :: \<open>(('a::domain\<times>'b::domain)\<times>'c::domain, 'a\<times>('b\<times>'c)) maps_hom\<close> where 
  assoc_hom: \<open>maps_hom assoc\<close> and
  assoc_apply: \<open>assoc (tensor_maps (tensor_maps a b) c) = (tensor_maps a (tensor_maps b c))\<close>

axiomatization lvalue :: \<open>('a,'b) maps_hom \<Rightarrow> bool\<close>
axiomatization where
  lvalue_hom: "lvalue F \<Longrightarrow> maps_hom F" and
  lvalue_comp: "lvalue F \<Longrightarrow> lvalue G \<Longrightarrow> lvalue (G \<circ> F)"  and
  lvalue_mult: "lvalue F \<Longrightarrow> F (comp_domain a b) = comp_domain (F a) (F b)"
  for F :: "('a::domain,'b::domain) maps_hom" and G :: "('b,'c::domain) maps_hom" 

axiomatization where
pair_lvalue_axiom: \<open>\<lbrakk>lvalue F; lvalue G; maps_hom p;
    \<And>a b. comp_domain (F a) (G b) = comp_domain (G b) (F a);
    \<And>a b. p (tensor_maps a b) = comp_domain (F a) (G b)\<rbrakk> \<Longrightarrow> lvalue p\<close>

bundle lvalue_notation begin
notation comp_domain (infixl "\<circ>\<^sub>d" 55)
notation tensor_maps (infixr "\<otimes>" 70)
end

bundle no_lvalue_notation begin
no_notation comp_domain (infixl "\<circ>\<^sub>d" 55)
no_notation tensor_maps (infixr "\<otimes>" 70)
end

end
