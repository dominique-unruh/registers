theory Classical
  imports Main
begin

class domain
instance prod :: (domain,domain) domain
  by intro_classes

type_synonym 'a domain_end = \<open>'a rel\<close>

abbreviation (input) comp_domain :: "'a::domain domain_end \<Rightarrow> 'a domain_end \<Rightarrow> 'a domain_end" where
  "comp_domain a b \<equiv> b O a"

lemma comp_domain_assoc: "comp_domain (comp_domain a b) c = comp_domain a (comp_domain b c)"
  by auto

(* TODO: category laws *)

type_synonym ('a,'b) maps_hom = \<open>'a domain_end \<Rightarrow> 'b domain_end\<close>

definition maps_hom :: \<open>('a::domain,'b::domain) maps_hom \<Rightarrow> bool\<close> where
  "maps_hom F \<longleftrightarrow> (\<exists>F'::'b\<times>'b \<rightharpoonup> 'a\<times>'a. F = (\<lambda>a. {xy. F' xy \<in> Some ` a}))"

definition "maps_hom_func F = (SOME F'. F = vimage F')"

lemma comp_maps_hom: "maps_hom F \<Longrightarrow> maps_hom G \<Longrightarrow> maps_hom (G \<circ> F)"
  unfolding maps_hom_def apply auto
  apply (rule_tac x=\<open>F' \<circ>\<^sub>m F'a\<close> in exI)
  apply (auto simp: o_def image_def intro!: ext)
  by (metis (mono_tags, hide_lams) map_comp_Some_iff surj_pair)
(* TODO category laws *)

type_synonym ('a,'b,'c) maps_2hom = \<open>'a domain_end \<Rightarrow> 'b domain_end \<Rightarrow> 'c domain_end\<close>

definition maps_2hom :: "('a::domain, 'b::domain, 'c::domain) maps_2hom \<Rightarrow> bool" where
  \<open>maps_2hom F2 \<longleftrightarrow> (\<exists>F2'. F2 = (\<lambda>r s. {xy. F2' xy \<in> Some ` (r \<times> s)}))\<close>

lemma maps_hom_2hom_comp: \<open>maps_2hom F2 \<Longrightarrow> maps_hom G \<Longrightarrow> maps_2hom (\<lambda>a b. G (F2 a b))\<close>
  unfolding maps_2hom_def maps_hom_def apply auto
  apply (rule_tac x=\<open>F2' \<circ>\<^sub>m F'\<close> in exI) apply (intro ext)
  apply (auto simp: map_comp_def image_def mem_Times_iff apfst_def o_def map_prod_def case_prod_beta)
  by (metis (mono_tags, hide_lams) Option.is_none_def is_none_simps(2) option.case_eq_if option.exhaust_sel prod.collapse)
lemma maps_2hom_hom_comp1: 
  assumes \<open>maps_2hom F2\<close> assumes \<open>maps_hom G\<close> shows \<open>maps_2hom (\<lambda>a b. F2 (G a) b)\<close>
proof -
  from \<open>maps_2hom F2\<close> 
  obtain F2' where F2: "F2 r s = {xy. F2' xy \<in> Some ` (r \<times> s)}" for r s
    by (metis maps_2hom_def)
  from \<open>maps_hom G\<close> 
  obtain G' where G: \<open>G a = {xy. G' xy \<in> Some ` a}\<close> for a
    by (metis maps_hom_def)
  define F2G' where \<open>F2G' = (\<lambda>(x,y). case G' x of None \<Rightarrow> None | Some x' \<Rightarrow> Some (x',y)) \<circ>\<^sub>m F2'\<close>
  have \<open>(x, y) \<in> F2 (G r) s \<Longrightarrow> F2G' (x, y) \<in> Some ` (r \<times> s)\<close> for x y r s
    unfolding F2 G F2G'_def by auto
  moreover have \<open>(x, y) \<in> F2 (G a) s \<close> 
    if F2G': \<open>F2G' (x, y) = Some ((ax, ay), (bx, by))\<close> and \<open>(ax, ay) \<in> a\<close> and \<open>(bx, by) \<in> s\<close>
    for a s x y ax ay bx "by"
  proof -
    obtain F2'1 F2'2 where F2': \<open>F2' (x, y) = Some (F2'1, F2'2)\<close>
      apply atomize_elim apply (cases \<open>F2' (x, y)\<close>) 
      using F2G'_def F2G' by auto
    show ?thesis
      apply (cases \<open>G' F2'1\<close>)
      using that
      by (auto simp: F2' F2 G F2G'_def)
  qed
  ultimately  show ?thesis
    unfolding maps_2hom_def
    apply (rule_tac exI[of _ F2G'])
    by (auto intro!: ext)
qed

lemma maps_2hom_sym: \<open>maps_2hom F2 \<Longrightarrow> maps_2hom (\<lambda>a b. F2 b a)\<close>
  unfolding maps_2hom_def apply auto
  apply (rule_tac x=\<open>map_option prod.swap o F2'\<close> in exI) apply (rule ext)
  by (auto simp: vimage_def mem_Times_iff prod.swap_def o_def prod.swap_def[abs_def])
lemma maps_2hom_left: \<open>maps_2hom F2 \<Longrightarrow> maps_hom (\<lambda>a. F2 a b)\<close>
  unfolding maps_2hom_def maps_hom_def apply auto 
  apply (rule_tac x=\<open>(\<lambda>(xya,xyb). if xyb\<in>b then Some xya else None) \<circ>\<^sub>m F2'\<close> in exI) apply (rule ext)
  apply (auto simp: vimage_def mem_Times_iff prod.swap_def o_def prod.swap_def[abs_def] image_def
      map_comp_def)
  by (smt (z3) case_prodE2 old.prod.case option.case_eq_if option.collapse option.disc_eq_case(2) option.distinct(1) option.inject)
  

lemma comp_2hom: "maps_2hom comp_domain"
  unfolding maps_2hom_def relcomp_unfold 
  apply (rule exI[of _ \<open>\<lambda>(x,z). \<close>])
  apply (intro ext) 
  apply simp
  unfolding maps_2hom_def apply autxo by -

definition tensor_maps :: \<open>'a domain_end \<Rightarrow> 'b domain_end \<Rightarrow> ('a\<times>'b) domain_end\<close> where



(* Tensor product on Maps *)
definition tensor_lift :: \<open>('a::domain, 'b::domain, 'c::domain) maps_2hom
                            \<Rightarrow> (('a\<times>'b, 'c) maps_hom)\<close>
definition tensor_maps :: \<open>'a domain_end \<Rightarrow> 'b domain_end \<Rightarrow> ('a\<times>'b) domain_end\<close>
lemma tensor_2hom: \<open>maps_2hom tensor_maps\<close> and
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
