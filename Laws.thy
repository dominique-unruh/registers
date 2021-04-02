theory Laws
  imports Axioms "HOL-Library.Rewrite" Misc
begin

no_notation Group.mult (infixl "\<otimes>\<index>" 70)

text \<open>This notation is only used inside this file\<close>
notation comp_update (infixl "*\<^sub>u" 55)
notation tensor_update (infixr "\<otimes>\<^sub>u" 70)

subsection \<open>Elementary facts\<close>

declare tensor_update_is_2hom[simp]
declare id_update_hom[simp]
declare id_update_left[simp]
declare id_update_right[simp]
declare lvalue_hom[simp]
declare lvalue_comp[simp]
declare lvalue_of_id[simp]

lemma update_2hom_o_hom_right_is_hom: \<open>update_2hom F2 \<Longrightarrow> update_hom G \<Longrightarrow> update_2hom (\<lambda>a b. F2 a (G b))\<close>
  apply (rule update_2hom_sym) apply (rule update_2hom_o_hom_left_is_hom) apply (rule update_2hom_sym) by simp

lemma update_2hom_right_is_hom: \<open>update_2hom F2 \<Longrightarrow> update_hom (\<lambda>b. F2 a b)\<close>
  apply (rule update_2hom_left_is_hom) by (rule update_2hom_sym)

subsection \<open>Lvalues\<close>

lemma id_update_tensor_lvalue[simp]:
  assumes \<open>lvalue F\<close>
  shows \<open>lvalue (\<lambda>a::'a::domain update. id_update \<otimes>\<^sub>u F a)\<close>
  using assms apply (rule lvalue_comp[unfolded o_def])
  by (simp add: lvalue_tensor_right)

lemma lvalue_tensor_id_update[simp]:
  assumes \<open>lvalue F\<close>
  shows \<open>lvalue (\<lambda>a::'a::domain update. F a \<otimes>\<^sub>u id_update)\<close>
  using assms apply (rule lvalue_comp[unfolded o_def])
  by (simp add: lvalue_tensor_left)

subsection \<open>Tensor product of homs\<close>

definition tensor_update_hom  (infixr "\<otimes>\<^sub>h" 70) where
  "tensor_update_hom F G = tensor_lift (\<lambda>a b. F a \<otimes>\<^sub>u G b)" 

lemma tensor_update_hom_hom_is_2hom[simp]:
  fixes F :: "'a::domain update \<Rightarrow> 'b::domain update" and G :: "'c::domain update \<Rightarrow> 'd::domain update"
  assumes \<open>update_hom F\<close> and \<open>update_hom G\<close>
  shows \<open>update_2hom (\<lambda>a b. F a \<otimes>\<^sub>u G b)\<close>
  apply (rule update_2hom_o_hom_left_is_hom, rule update_2hom_o_hom_right_is_hom)
  by (rule tensor_update_is_2hom assms)+

lemma tensor_update_hom_is_hom: 
  fixes F :: "'a::domain update \<Rightarrow> 'b::domain update" and G :: "'c::domain update \<Rightarrow> 'd::domain update"
  shows "update_hom F \<Longrightarrow> update_hom G \<Longrightarrow> update_hom (F \<otimes>\<^sub>h G)"
  unfolding tensor_update_hom_def apply (rule tensor_lift_hom) by simp

lemma tensor_update_hom_apply[simp]:
  fixes F :: "'a::domain update \<Rightarrow> 'b::domain update" and G :: "'c::domain update \<Rightarrow> 'd::domain update"
  assumes \<open>update_hom F\<close> and \<open>update_hom G\<close>
  shows "(F \<otimes>\<^sub>h G) (a \<otimes>\<^sub>u b) = F a \<otimes>\<^sub>u G b"
  unfolding tensor_update_hom_def 
  using tensor_lift_correct tensor_update_hom_hom_is_2hom[OF assms] 
  by metis

lemma update_hom_tensor_is_2hom[simp]: 
  fixes F :: "('a::domain \<times> 'b::domain) update \<Rightarrow> 'c::domain update"
  shows \<open>update_hom F \<Longrightarrow> update_2hom (\<lambda>a b. F (a \<otimes>\<^sub>u b))\<close>
  using tensor_update_is_2hom by (rule update_hom_o_2hom_is_2hom)

lemma update_hom_tensor_left_is_hom[simp]: "update_hom ((\<otimes>\<^sub>u) a :: 'b::domain update \<Rightarrow> _)" 
  for a :: "'a::domain update"
  apply (rule update_2hom_right_is_hom)
  by (simp add: update_2hom_right_is_hom)

lemma update_hom_tensor_right_is_hom[simp]: "update_hom (\<lambda>a::'a::domain update. (\<otimes>\<^sub>u) a b)"
  for b :: "'b::domain update"
  by (simp add: update_2hom_left_is_hom)

lemma tensor_extensionality3: 
  fixes F G :: \<open>('a::domain\<times>'b::domain\<times>'c::domain) update \<Rightarrow> 'd::domain update\<close>
  assumes [simp]: \<open>update_hom F\<close> \<open>update_hom G\<close>
  assumes "\<And>f g h. F (f \<otimes>\<^sub>u g \<otimes>\<^sub>u h) = G (f \<otimes>\<^sub>u g \<otimes>\<^sub>u h)"
  shows "F = G"
proof -
  from assms
  have "(F \<circ> (\<otimes>\<^sub>u) a) (b \<otimes>\<^sub>u c) = (G \<circ> (\<otimes>\<^sub>u) a) (b \<otimes>\<^sub>u c)" for a b c
    by auto
  then have "F \<circ> (\<otimes>\<^sub>u) a = G \<circ> (\<otimes>\<^sub>u) a" for a
    apply (rule tensor_extensionality[rotated -1])
    by (intro comp_update_hom; simp)+
  then have "F (a \<otimes>\<^sub>u bc) = G (a \<otimes>\<^sub>u bc)" for a bc
    by (meson o_eq_elim)
  then show ?thesis
    by (rule tensor_extensionality[rotated -1]; simp)
qed

lemma tensor_extensionality3':
  fixes F G :: \<open>(('a::domain\<times>'b::domain)\<times>'c::domain) update \<Rightarrow> 'd::domain update\<close>
  assumes [simp]: \<open>update_hom F\<close> \<open>update_hom G\<close>
  assumes "\<And>f g h. F ((f \<otimes>\<^sub>u g) \<otimes>\<^sub>u h) = G ((f \<otimes>\<^sub>u g) \<otimes>\<^sub>u h)"
  shows "F = G"
proof -
  from assms
  have "(F \<circ> (\<lambda>x. x \<otimes>\<^sub>u c)) (a \<otimes>\<^sub>u b) = (G \<circ> (\<lambda>x. x \<otimes>\<^sub>u c)) (a \<otimes>\<^sub>u b)" for a b c
    by auto
  then have "F \<circ> (\<lambda>x. x \<otimes>\<^sub>u c) = G \<circ> (\<lambda>x. x \<otimes>\<^sub>u c)" for c
    apply (rule tensor_extensionality[rotated -1])
    by (intro comp_update_hom; simp)+
  then have "F (ab \<otimes>\<^sub>u c) = G (ab \<otimes>\<^sub>u c)" for ab c
    by (meson o_eq_elim)
  then show ?thesis
    by (rule tensor_extensionality[rotated -1]; simp)
qed


subsection \<open>Swap and assoc\<close>

definition \<open>swap = tensor_lift (\<lambda>a b. b \<otimes>\<^sub>u a)\<close>

lemma swap_is_hom[simp]: "update_hom swap"
  unfolding swap_def apply (rule tensor_lift_hom) 
  apply (rule update_2hom_sym) by (fact tensor_update_is_2hom)

lemma swap_apply[simp]: "swap (a \<otimes>\<^sub>u b) = (b \<otimes>\<^sub>u a)"
  unfolding swap_def 
  apply (rule tensor_lift_correct[THEN fun_cong, THEN fun_cong])
  apply (rule update_2hom_sym) by (fact tensor_update_is_2hom)

subsection \<open>Pairs and compatibility\<close>

definition compatible :: \<open>('a::domain update \<Rightarrow> 'c::domain update)
                       \<Rightarrow> ('b::domain update \<Rightarrow> 'c update) \<Rightarrow> bool\<close> where
  \<open>compatible F G \<longleftrightarrow> lvalue F \<and> lvalue G \<and> (\<forall>a b. F a *\<^sub>u G b = G b *\<^sub>u F a)\<close>

lemma compatibleI:
  assumes "lvalue F" and "lvalue G"
  assumes \<open>\<And>a b. (F a) *\<^sub>u (G b) = (G b) *\<^sub>u (F a)\<close>
  shows "compatible F G"
  using assms unfolding compatible_def by simp

lemma swap_lvalues:
  assumes "compatible R S"
  shows "R a *\<^sub>u S b = S b *\<^sub>u R a"
  using assms unfolding compatible_def by metis

lemma compatible_sym: "compatible x y \<Longrightarrow> compatible y x"
  by (simp add: compatible_def)

definition lvalue_pair :: \<open>('a::domain update \<Rightarrow> 'c::domain update) \<Rightarrow> ('b::domain update \<Rightarrow> 'c update)
         \<Rightarrow> (('a\<times>'b) update \<Rightarrow> 'c update)\<close> ("'(_;_')") where
  \<open>(F; G) = tensor_lift (\<lambda>a b. F a *\<^sub>u G b)\<close>

lemma hom_comp_update_hom_is_2hom[simp]:
  assumes \<open>update_hom F\<close> and \<open>update_hom G\<close>
  shows \<open>update_2hom (\<lambda>a b. F a *\<^sub>u G b)\<close>
  apply (rule update_2hom_o_hom_left_is_hom, rule update_2hom_o_hom_right_is_hom)
  by (rule comp_update_is_2hom assms)+

lemma lvalue_pair_is_hom[simp]:
  assumes "update_hom F" and "update_hom G"
  shows "update_hom (F; G)"
  unfolding lvalue_pair_def apply (rule tensor_lift_hom) using assms by simp

lemma lvalue_pair_apply:
  assumes \<open>update_hom F\<close> and \<open>update_hom G\<close>
  shows \<open>(F; G) (a \<otimes>\<^sub>u b) = (F a) *\<^sub>u (G b)\<close>
  unfolding lvalue_pair_def 
  using tensor_lift_correct hom_comp_update_hom_is_2hom[OF assms]
  by metis

lemma lvalue_pair_apply':
  assumes \<open>compatible F G\<close>
  shows \<open>(F; G) (a \<otimes>\<^sub>u b) = (G b) *\<^sub>u (F a)\<close>
  apply (subst lvalue_pair_apply)
  using assms by (auto simp: compatible_def intro: lvalue_hom)

lemma pair_lvalue[simp]:
  assumes "compatible F G"
  shows "lvalue (F; G)"
  apply (rule pair_lvalue_axiom[where F=F and G=G and p=\<open>(F; G)\<close>])
  using assms by (auto simp: lvalue_pair_apply compatible_def)


lemma compatible3[simp]:
  assumes [simp]: "compatible F G" and "compatible G H" and "compatible F H"
  shows "compatible (F; G) H"
proof (rule compatibleI)
  have [simp]: \<open>lvalue F\<close> \<open>lvalue G\<close> \<open>lvalue H\<close>
    using assms compatible_def by auto
  then have [simp]: \<open>update_hom F\<close> \<open>update_hom G\<close> \<open>update_hom H\<close>
    using lvalue_hom by blast+
  have "((F; G); H) ((f \<otimes>\<^sub>u g) \<otimes>\<^sub>u h) = (H; (F; G)) (h \<otimes>\<^sub>u (f \<otimes>\<^sub>u g))" for f g h
    using assms apply (simp add: lvalue_pair_apply compatible_def comp_update_assoc)
    by (metis comp_update_assoc)
  then have "(((F; G); H) \<circ> swap \<circ> (\<otimes>\<^sub>u) h) (f \<otimes>\<^sub>u g)
           = ((H; (F; G)) \<circ> (\<otimes>\<^sub>u) h) (f \<otimes>\<^sub>u g)" for f g h
    by auto
  then have *: "((F; G); H) \<circ> swap \<circ> (\<otimes>\<^sub>u) h = (H; (F; G)) \<circ> (\<otimes>\<^sub>u) h" for h
    apply (rule tensor_extensionality[rotated -1])
    by (intro comp_update_hom lvalue_pair_is_hom; simp)+
  have "((F; G); H) (fg \<otimes>\<^sub>u h) = (H; (F; G)) (h \<otimes>\<^sub>u fg)" for fg h
    using *
    using comp_eq_dest_lhs by fastforce
  then show "(F; G) fg *\<^sub>u (H h) = (H h) *\<^sub>u (F; G) fg" for fg h
    unfolding compatible_def by (simp add: lvalue_pair_apply)
  show "lvalue H" and  "lvalue (F; G)"
    by simp_all
qed

lemma compatible3'[simp]:
  assumes "compatible F G" and "compatible G H" and "compatible F H"
  shows "compatible F (G; H)"
  apply (rule compatible_sym)
  apply (rule compatible3)
  using assms by (auto simp: compatible_sym)

lemma compatible_comp_left[simp]: "compatible F G \<Longrightarrow> lvalue H \<Longrightarrow> compatible (F \<circ> H) G"
  by (simp add: compatible_def)

lemma compatible_comp_right[simp]: "compatible F G \<Longrightarrow> lvalue H \<Longrightarrow> compatible F (G \<circ> H)"
  by (simp add: compatible_def)

lemma compatible_comp_inner[simp]: 
  "compatible F G \<Longrightarrow> lvalue H \<Longrightarrow> compatible (H \<circ> F) (H \<circ> G)"
  by (smt (verit, best) comp_apply compatible_def lvalue_comp lvalue_mult)

lemma compatible_lvalue1: \<open>compatible F G \<Longrightarrow> lvalue F\<close>
  by (simp add: compatible_def)
lemma compatible_lvalue2: \<open>compatible F G \<Longrightarrow> lvalue G\<close>
  by (simp add: compatible_def)

lemma pair_o_tensor:
  assumes "compatible A B" and [simp]: \<open>update_hom C\<close> and [simp]: \<open>update_hom D\<close>
  shows "(A; B) o (C \<otimes>\<^sub>h D) = (A o C; B o D)"
proof (rule tensor_extensionality)
  have [simp]: \<open>update_hom A\<close>
    by (metis assms(1) compatible_lvalue1 lvalue_hom)
  have [simp]: \<open>update_hom B\<close>
    by (metis (mono_tags, lifting) assms(1) compatible_lvalue2 lvalue_hom)
  show \<open>update_hom ((A; B) \<circ> (C \<otimes>\<^sub>h D))\<close>
    by (metis assms(1) assms(2) assms(3) comp_update_hom compatible_lvalue1 compatible_lvalue2 
              lvalue_hom lvalue_pair_is_hom tensor_update_hom_is_hom)
  show \<open>update_hom (A \<circ> C; B \<circ> D)\<close>
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) comp_update_hom compatible_lvalue1 compatible_lvalue2 lvalue_hom lvalue_pair_is_hom)

  show \<open>((A; B) \<circ> (C \<otimes>\<^sub>h D)) (a \<otimes>\<^sub>u b) = (A \<circ> C; B \<circ> D) (a \<otimes>\<^sub>u b)\<close> for a b
    by (simp add: lvalue_pair_apply comp_update_hom)
qed

lemma pair_o_swap[simp]:
  assumes "compatible A B"
  shows "(A; B) o swap = (B; A)"
proof (rule tensor_extensionality)
  have [simp]: "update_hom A" "update_hom B"
    apply (metis (no_types, hide_lams) assms compatible_lvalue1 lvalue_hom)
    by (metis (full_types) assms compatible_lvalue2 lvalue_hom)
  then show \<open>update_hom ((A; B) \<circ> swap)\<close>
    by (metis (no_types, hide_lams) comp_update_hom lvalue_pair_is_hom swap_is_hom)
  show \<open>update_hom (B; A)\<close>
    by (metis (no_types, lifting) assms compatible_sym lvalue_hom pair_lvalue)
  show \<open>((A; B) \<circ> swap) (a \<otimes>\<^sub>u b) = (B; A) (a \<otimes>\<^sub>u b)\<close> for a b
    (* Without the "only:", we would not need the "apply subst",
       but that proof fails when instantiated in Classical.thy *)
    apply (simp only: o_def swap_apply)
    apply (subst lvalue_pair_apply, simp, simp)
    apply (subst lvalue_pair_apply, simp, simp)
    by (metis (no_types, lifting) assms compatible_def)
qed

lemma compatible_tensor_id_update_left[simp]:
  fixes F :: "'a::domain update \<Rightarrow> 'c::domain update" and G :: "'b::domain update \<Rightarrow> 'c::domain update"
  assumes "compatible F G"
  shows "compatible (\<lambda>a. id_update \<otimes>\<^sub>u F a) (\<lambda>a. id_update \<otimes>\<^sub>u G a)"
  using assms apply (rule compatible_comp_inner[unfolded o_def])
  by (simp add: lvalue_tensor_right)
  
lemma compatible_tensor_id_update_right[simp]:
  fixes F :: "'a::domain update \<Rightarrow> 'c::domain update" and G :: "'b::domain update \<Rightarrow> 'c::domain update"
  assumes "compatible F G"
  shows "compatible (\<lambda>a. F a \<otimes>\<^sub>u id_update) (\<lambda>a. G a \<otimes>\<^sub>u id_update)"
  using assms apply (rule compatible_comp_inner[unfolded o_def])
  by (simp add: lvalue_tensor_left)

lemma compatible_tensor_id_update_rl[simp]:
  assumes "lvalue F" and "lvalue G"
  shows "compatible (\<lambda>a. F a \<otimes>\<^sub>u id_update) (\<lambda>a. id_update \<otimes>\<^sub>u G a)"
  apply (rule compatibleI)
  using assms by (auto simp: tensor_update_mult)
  
lemma compatible_tensor_id_update_lr[simp]:
  assumes "lvalue F" and "lvalue G"
  shows "compatible (\<lambda>a. id_update \<otimes>\<^sub>u F a) (\<lambda>a. G a \<otimes>\<^sub>u id_update)"
  apply (rule compatibleI)
  using assms by (auto simp: tensor_update_mult)

subsection \<open>Fst and Snd\<close>

definition Fst where \<open>Fst a = a \<otimes>\<^sub>u id_update\<close>
definition Snd where \<open>Snd a = id_update \<otimes>\<^sub>u a\<close>

lemma swap_o_Fst: "swap o Fst = Snd"
  by (auto simp add: Fst_def Snd_def)
lemma swap_o_Snd: "swap o Snd = Fst"
  by (auto simp add: Fst_def Snd_def)

lemma lvalue_Fst[simp]: \<open>lvalue Fst\<close>
  unfolding Fst_def by (rule lvalue_tensor_left)

lemma lvalue_Snd[simp]: \<open>lvalue Snd\<close>
  unfolding Snd_def by (rule lvalue_tensor_right)

lemma compatible_Fst_Snd[simp]: \<open>compatible Fst Snd\<close>
  apply (rule compatibleI, simp, simp)
  by (simp add: Fst_def Snd_def tensor_update_mult)

lemmas compatible_Snd_Fst[simp] = compatible_Fst_Snd[THEN compatible_sym]

lemma pair_Fst_Snd: \<open>(Fst; Snd) = id\<close>
  apply (rule tensor_extensionality)
  by (simp_all add: lvalue_pair_apply Fst_def Snd_def tensor_update_mult)

lemma pair_Snd_Fst: \<open>(Snd; Fst) = swap\<close>
  apply (rule tensor_extensionality)
  by (simp_all add: lvalue_pair_apply Fst_def Snd_def tensor_update_mult)

lemma lvalue_swap: \<open>lvalue swap\<close>
  by (simp flip: pair_Snd_Fst)

lemma lvalue_Fst_lvalue_Snd[simp]: 
  assumes \<open>lvalue F\<close>
  shows \<open>(F o Fst; F o Snd) = F\<close>
  apply (rule tensor_extensionality)
  using assms by (auto simp: lvalue_pair_apply Fst_def Snd_def lvalue_mult tensor_update_mult)

lemma lvalue_Snd_lvalue_Fst[simp]: 
  assumes \<open>lvalue F\<close>
  shows \<open>(F o Snd; F o Fst) = F o swap\<close>
  apply (rule tensor_extensionality)
  using assms by (auto simp: lvalue_pair_apply Fst_def Snd_def lvalue_mult tensor_update_mult lvalue_swap)

section \<open>Associativity of the tensor product\<close>

definition assoc :: \<open>(('a::domain\<times>'b::domain)\<times>'c::domain) update \<Rightarrow> ('a\<times>('b\<times>'c)) update\<close> where 
  \<open>assoc = ((Fst; Snd o Fst); Snd o Snd)\<close>

lemma assoc_is_hom[simp]: \<open>update_hom assoc\<close>
  by (auto simp: assoc_def)

lemma assoc_apply: \<open>assoc ((a \<otimes>\<^sub>u b) \<otimes>\<^sub>u c) = (a \<otimes>\<^sub>u (b \<otimes>\<^sub>u c))\<close>
  by (auto simp: assoc_def lvalue_pair_apply Fst_def Snd_def tensor_update_mult)

definition assoc' :: \<open>('a\<times>('b\<times>'c)) update \<Rightarrow> (('a::domain\<times>'b::domain)\<times>'c::domain) update\<close> where 
  \<open>assoc' = (Fst o Fst; (Fst o Snd; Snd))\<close>

lemma assoc'_is_hom[simp]: \<open>update_hom assoc'\<close>
  by (auto simp: assoc'_def)

lemma assoc'_apply: \<open>assoc' (a \<otimes>\<^sub>u (b \<otimes>\<^sub>u c)) =  ((a \<otimes>\<^sub>u b) \<otimes>\<^sub>u c)\<close>
  by (auto simp: assoc'_def lvalue_pair_apply Fst_def Snd_def tensor_update_mult)

lemma lvalue_assoc: \<open>lvalue assoc\<close>
  unfolding assoc_def
  by force

lemma lvalue_assoc': \<open>lvalue assoc'\<close>
  unfolding assoc'_def 
  by force

lemma pair_o_assoc[simp]:
  assumes [simp]: \<open>update_hom F\<close> \<open>update_hom G\<close> \<open>update_hom H\<close>
  shows \<open>(F; (G; H)) \<circ> assoc = ((F; G); H)\<close>
proof (rule tensor_extensionality3')
  show \<open>update_hom ((F; (G; H)) \<circ> assoc)\<close>
    by (metis assms(1) assms(2) assms(3) assoc_is_hom comp_update_hom lvalue_pair_is_hom)
  show \<open>update_hom ((F; G); H)\<close>
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) lvalue_pair_is_hom)
  show \<open>((F; (G; H)) \<circ> assoc) ((f \<otimes>\<^sub>u g) \<otimes>\<^sub>u h) = ((F; G); H) ((f \<otimes>\<^sub>u g) \<otimes>\<^sub>u h)\<close> for f g h
    by (simp add: lvalue_pair_apply assoc_apply comp_update_assoc)
qed

lemma pair_o_assoc'[simp]:
  assumes [simp]: \<open>update_hom F\<close> \<open>update_hom G\<close> \<open>update_hom H\<close>
  shows \<open>((F; G); H) \<circ> assoc' = (F; (G; H))\<close>
proof (rule tensor_extensionality3)
  show \<open>update_hom (((F; G); H) \<circ> assoc')\<close>
    by (metis (no_types, hide_lams) assms(1) assms(2) assms(3) assoc'_is_hom comp_update_hom lvalue_pair_is_hom)
  show \<open>update_hom (F; (G; H))\<close>
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) lvalue_pair_is_hom)
  show \<open>(((F; G); H) \<circ> assoc') (f \<otimes>\<^sub>u g \<otimes>\<^sub>u h) = (F; (G; H)) (f \<otimes>\<^sub>u g \<otimes>\<^sub>u h)\<close> for f g h
    by (simp add: lvalue_pair_apply assoc'_apply comp_update_assoc)
qed

subsection \<open>Compatibility simplification\<close>

(* The simproc compatibility_warn produces helpful warnings for "compatible x y"
   subgoals that are probably unsolvable due to missing declarations of 
   variable compatibility facts. Same for "lvalue x" subgoals. *)
simproc_setup "compatibility_warn" ("compatible x y" | "lvalue x") = \<open>
let val thy_string = Markup.markup (Theory.get_markup \<^theory>) (Context.theory_name \<^theory>)
in
fn m => fn ctxt => fn ct => let
  val (x,y) = case Thm.term_of ct of
                 Const(\<^const_name>\<open>compatible\<close>,_ ) $ x $ y => (x, SOME y)
               | Const(\<^const_name>\<open>lvalue\<close>,_ ) $ x => (x, NONE)
  val str : string lazy = Lazy.lazy (fn () => Syntax.string_of_term ctxt (Thm.term_of ct))
  fun w msg = warning (msg ^ "\n(Disable these warnings with: using [[simproc del: "^thy_string^".compatibility_warn]])")
  (* val _ = \<^print> (m,ctxt,ct) *)
  val _ = case (x,y) of
        (Free(n,T), SOME (Free(n',T'))) => 
            if String.isPrefix ":" n orelse String.isPrefix ":" n' then 
                      w ("Simplification subgoal " ^ Lazy.force str ^ " contains a bound variable.\n" ^
                      "Try to add some assumptions that makes this goal solvable by the simplifier")
            else if n=n' then (if T=T' then () 
                          else w ("In simplification subgoal " ^ Lazy.force str ^ 
                               ", variables have same name and different types.\n" ^
                               "Probably something is wrong."))
                    else w ("Simplification subgoal " ^ Lazy.force str ^ 
                            " occurred but cannot be solved.\n" ^
                            "Please add assumption/fact  [simp]: \<open>" ^ Lazy.force str ^ 
                            "\<close>  somewhere.")
(*       | (_, SOME _) => w ("Simplification subgoal " ^ Lazy.force str ^ 
                    "\ncannot be reduced to a compatibility of two variables (such as \<open>compatibility x y\<close>).\n" ^
                    "Try adding a simplification rule that breaks it down (such as, e.g., " ^ @{fact compatible3} ^ ").") *)
      | (Free(n,T), NONE) => 
            if String.isPrefix ":" n then 
                      w ("Simplification subgoal '" ^ Lazy.force str ^ "' contains a bound variable.\n" ^
                      "Try to add some assumptions that makes this goal solvable by the simplifier")
            else w ("Simplification subgoal " ^ Lazy.force str ^ " occurred but cannot be solved.\n" ^
                    "Please add assumption/fact  [simp]: \<open>" ^ Lazy.force str ^ "\<close>  somewhere.")
(*       | (_, NONE) => w ("Simplification subgoal " ^ Lazy.force str ^ 
                    "\ncannot be reduced to a judgment about a single variable (such as \<open>lvalue x\<close>).\n" ^
                    "Try adding a simplification rule that breaks it down (such as, e.g., " ^ @{fact lvalue_comp} ^ ").") *)
      | _ => ()
  in NONE end
end\<close>


(* Declares the attribute [compatible]. If applied to a conjunction 
   of "compatible x y" facts, it will add all of them to the simplifier
   (as [simp] does), but additionally add all "lvalue x", "lvalue y" facts. *)
setup \<open>
let 
fun add (thm:thm) results = 
  Net.insert_term (K true) (Thm.concl_of thm, thm) results
  handle Net.INSERT => results
fun collect thm results = case Thm.concl_of thm of
  Const(\<^const_name>\<open>Trueprop\<close>,_) $ (Const(\<^const_name>\<open>conj\<close>,_) $ _ $ _) => 
    collect (@{thm conjunct1} OF [thm]) (collect (@{thm conjunct2} OF [thm]) results)
  | Const(\<^const_name>\<open>Trueprop\<close>,_) $ (Const(\<^const_name>\<open>compatible\<close>,_) $ _ $ _) =>
    collect (@{thm compatible_lvalue1} OF [thm]) (collect (@{thm compatible_lvalue2} OF [thm]) (add thm results))
  | _ => add thm results
fun declare thm context = let
  val thms = collect thm (Net.empty) |> Net.entries
  in Simplifier.map_ss (fn ctxt => ctxt addsimps thms) context end
in
Attrib.setup \<^binding>\<open>compatible\<close>
 (Scan.succeed (Thm.declaration_attribute declare))
  "Add 'compatible x y' style rules to simplifier. (Also adds 'lvalue x', 'lvalue y')"
end
\<close>



subsection \<open>Notation\<close>

no_notation comp_update (infixl "*\<^sub>u" 55)
no_notation tensor_update (infixr "\<otimes>\<^sub>u" 70)

bundle lvalue_notation begin
notation tensor_update_hom (infixr "\<otimes>\<^sub>h" 70)
notation lvalue_pair ("'(_;_')")
end

bundle no_lvalue_notation begin
no_notation tensor_update_hom (infixr "\<otimes>\<^sub>h" 70)
no_notation lvalue_pair ("'(_;_')")
end

end
