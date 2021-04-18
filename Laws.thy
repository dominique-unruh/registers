section \<open>Generic laws about lvalues\<close>

theory Laws
  imports Axioms "HOL-Library.Rewrite" Misc
begin

no_notation Group.mult (infixl "\<otimes>\<index>" 70)

text \<open>This notation is only used inside this file\<close>
notation comp_update (infixl "*\<^sub>u" 55)
notation tensor_update (infixr "\<otimes>\<^sub>u" 70)
notation lvalue_pair ("'(_;_')")

subsection \<open>Elementary facts\<close>

declare id_update_hom[simp]
declare id_update_left[simp]
declare id_update_right[simp]
declare lvalue_hom[simp]
declare lvalue_comp[simp]
declare lvalue_of_id[simp]
declare lvalue_tensor_left[simp]
declare lvalue_tensor_right[simp]
declare update_hom_mult_right[simp]
declare update_hom_mult_left[simp]

subsection \<open>Lvalues\<close>

lemma id_update_tensor_lvalue[simp]:
  assumes \<open>lvalue F\<close>
  shows \<open>lvalue (\<lambda>a::'a::domain update. id_update \<otimes>\<^sub>u F a)\<close>
  using assms apply (rule lvalue_comp[unfolded o_def])
  by simp

lemma lvalue_tensor_id_update[simp]:
  assumes \<open>lvalue F\<close>
  shows \<open>lvalue (\<lambda>a::'a::domain update. F a \<otimes>\<^sub>u id_update)\<close>
  using assms apply (rule lvalue_comp[unfolded o_def])
  by (simp add: lvalue_tensor_left)

subsection \<open>Tensor product of homs\<close>

(* TODO: rename \<rightarrow> lvalue_tensor *)
definition tensor_update_hom  (infixr "\<otimes>\<^sub>h" 70) where
  "tensor_update_hom F G = lvalue_pair (\<lambda>a. tensor_update (F a) id_update) (\<lambda>b. tensor_update id_update (G b))"

lemma tensor_update_hom_is_hom: 
  fixes F :: "'a::domain update \<Rightarrow> 'b::domain update" and G :: "'c::domain update \<Rightarrow> 'd::domain update"
  shows "lvalue F \<Longrightarrow> lvalue G \<Longrightarrow> lvalue (F \<otimes>\<^sub>h G)"
  unfolding tensor_update_hom_def
  apply (rule lvalue_pair_lvalue)
  by (simp_all add: tensor_update_mult)

lemma tensor_update_hom_apply[simp]:
  fixes F :: "'a::domain update \<Rightarrow> 'b::domain update" and G :: "'c::domain update \<Rightarrow> 'd::domain update"
  assumes \<open>lvalue F\<close> and \<open>lvalue G\<close>
  shows "(F \<otimes>\<^sub>h G) (a \<otimes>\<^sub>u b) = F a \<otimes>\<^sub>u G b"
  unfolding tensor_update_hom_def
  apply (subst lvalue_pair_apply)
  unfolding tensor_update_hom_def 
  by (simp_all add: assms tensor_update_mult)

lemma update_hom_tensor_left_is_hom[simp]: "update_hom ((\<otimes>\<^sub>u) a :: 'b::domain update \<Rightarrow> _)" 
  for a :: "'a::domain update"
  sorry

lemma update_hom_tensor_right_is_hom[simp]: "update_hom (\<lambda>a::'a::domain update. (\<otimes>\<^sub>u) a b)"
  for b :: "'b::domain update"
  sorry

definition "update_basis (_::'b::domain itself) A \<longleftrightarrow> 
  (\<forall>F G :: 'a::domain update \<Rightarrow> 'b update. update_hom F \<longrightarrow> update_hom G \<longrightarrow> (\<forall>x\<in>A. F x = G x) \<longrightarrow> F = G)"

lemma update_basis_UNIV[simp]: \<open>update_basis TYPE(_) UNIV\<close>
  unfolding update_basis_def by auto

lemma update_basis_mono: \<open>A \<subseteq> B \<Longrightarrow> update_basis TYPE('a::domain) A \<Longrightarrow> update_basis TYPE('a) B\<close>
  unfolding update_basis_def by (meson in_mono) 

lemma lvalue_eqI: \<open>update_basis TYPE('b::domain) A \<Longrightarrow> update_hom F \<Longrightarrow> update_hom G \<Longrightarrow> (\<And>x. x\<in>A \<Longrightarrow> F x = G x) \<Longrightarrow> F = (G::_ \<Rightarrow> 'b update)\<close>
  unfolding update_basis_def by auto

lemma update_basis_tensor:
  fixes A :: \<open>'a::domain update set\<close> and B :: \<open>'b::domain update set\<close>
  assumes [simp]: \<open>update_basis TYPE('c::domain) A\<close>
  assumes [simp]: \<open>update_basis TYPE('c) B\<close>
  shows \<open>update_basis TYPE('c) {a \<otimes>\<^sub>u b | a b. a\<in>A \<and> b\<in>B}\<close>
proof (unfold update_basis_def, intro allI impI)
  fix F G :: \<open>('a\<times>'b) update \<Rightarrow> 'c update\<close>
  assume [simp]: \<open>update_hom F\<close> \<open>update_hom G\<close>
  have [simp]: \<open>update_hom (\<lambda>x. F (a \<otimes>\<^sub>u x))\<close> for a
    using _ \<open>update_hom F\<close> apply (rule comp_update_hom[unfolded o_def])
    by simp
  have [simp]: \<open>update_hom (\<lambda>x. G (a \<otimes>\<^sub>u x))\<close> for a
    using _ \<open>update_hom G\<close> apply (rule comp_update_hom[unfolded o_def])
    by simp
  have [simp]: \<open>update_hom (\<lambda>x. F (x \<otimes>\<^sub>u b))\<close> for b
    using _ \<open>update_hom F\<close> apply (rule comp_update_hom[unfolded o_def])
    by simp
  have [simp]: \<open>update_hom (\<lambda>x. G (x \<otimes>\<^sub>u b))\<close> for b
    using _ \<open>update_hom G\<close> apply (rule comp_update_hom[unfolded o_def])
    by simp

  assume \<open>\<forall>x\<in>{a \<otimes>\<^sub>u b |a b. a\<in>A \<and> b\<in>B}. F x = G x\<close>
  then have EQ: \<open>F (a \<otimes>\<^sub>u b) = G (a \<otimes>\<^sub>u b)\<close> if \<open>a \<in> A\<close> and \<open>b \<in> B\<close> for a b
    using that by auto
  then have \<open>F (a \<otimes>\<^sub>u b) = G (a \<otimes>\<^sub>u b)\<close> if \<open>a \<in> A\<close> for a b
    apply (rule lvalue_eqI[where A=B, THEN fun_cong, where x=b, rotated -1])
    using that by auto
  then have \<open>F (a \<otimes>\<^sub>u b) = G (a \<otimes>\<^sub>u b)\<close> for a b
    apply (rule lvalue_eqI[where A=A, THEN fun_cong, where x=a, rotated -1])
    by auto
  then show "F = G"
    apply (rule tensor_extensionality[rotated -1])
    by auto
qed

(* Easier to apply using 'rule' than update_basis_tensor *)
lemma update_basis_tensor':
  fixes A :: \<open>'a::domain update set\<close> and B :: \<open>'b::domain update set\<close>
  assumes \<open>update_basis TYPE('c::domain) A\<close>
  assumes \<open>update_basis TYPE('c) B\<close>
  assumes \<open>C = {a \<otimes>\<^sub>u b | a b. a\<in>A \<and> b\<in>B}\<close>
  shows \<open>update_basis TYPE('c) C\<close>
  using assms
  by (simp add: update_basis_tensor)

lemma tensor_extensionality3: 
  fixes F G :: \<open>('a::domain\<times>'b::domain\<times>'c::domain) update \<Rightarrow> 'd::domain update\<close>
  assumes [simp]: \<open>lvalue F\<close> \<open>lvalue G\<close>
  assumes "\<And>f g h. F (f \<otimes>\<^sub>u g \<otimes>\<^sub>u h) = G (f \<otimes>\<^sub>u g \<otimes>\<^sub>u h)"
  shows "F = G"
proof (rule lvalue_eqI[where A=\<open>{a\<otimes>\<^sub>ub\<otimes>\<^sub>uc| a b c. True}\<close>])
  have \<open>update_basis TYPE('d) {b \<otimes>\<^sub>u c |b c. True}\<close>
    apply (rule update_basis_tensor'[where A=UNIV and B=UNIV])
    by auto
  then show \<open>update_basis TYPE('d) {a \<otimes>\<^sub>u b \<otimes>\<^sub>u c |a b c. True}\<close>
    apply (rule_tac update_basis_tensor'[where A=UNIV and B=\<open>{b\<otimes>\<^sub>uc| b c. True}\<close>])
    by auto
  show \<open>update_hom F\<close> \<open>update_hom G\<close> by auto
  show \<open>x \<in> {a \<otimes>\<^sub>u b \<otimes>\<^sub>u c |a b c. True} \<Longrightarrow> F x = G x\<close> for x
    using assms(3) by auto
qed

lemma tensor_extensionality3': 
  fixes F G :: \<open>(('a::domain\<times>'b::domain)\<times>'c::domain) update \<Rightarrow> 'd::domain update\<close>
  assumes [simp]: \<open>lvalue F\<close> \<open>lvalue G\<close>
  assumes "\<And>f g h. F ((f \<otimes>\<^sub>u g) \<otimes>\<^sub>u h) = G ((f \<otimes>\<^sub>u g) \<otimes>\<^sub>u h)"
  shows "F = G"
proof (rule lvalue_eqI[where A=\<open>{(a\<otimes>\<^sub>ub)\<otimes>\<^sub>uc| a b c. True}\<close>])
  have \<open>update_basis TYPE('d) {a \<otimes>\<^sub>u b | a b. True}\<close>
    apply (rule update_basis_tensor'[where A=UNIV and B=UNIV])
    by auto
  then show \<open>update_basis TYPE('d) {(a \<otimes>\<^sub>u b) \<otimes>\<^sub>u c |a b c. True}\<close>
    apply (rule_tac update_basis_tensor'[where B=UNIV and A=\<open>{a\<otimes>\<^sub>ub| a b. True}\<close>])
    by auto
  show \<open>update_hom F\<close> \<open>update_hom G\<close> by auto
  show \<open>x \<in> {(a \<otimes>\<^sub>u b) \<otimes>\<^sub>u c |a b c. True} \<Longrightarrow> F x = G x\<close> for x
    using assms(3) by auto
qed



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

lemma pair_lvalue[simp]:
  assumes "compatible F G"
  shows "lvalue (F; G)"
  by (metis assms compatible_def lvalue_pair_lvalue)

lemma lvalue_pair_apply:
  assumes \<open>compatible F G\<close>
  shows \<open>(F; G) (a \<otimes>\<^sub>u b) = (F a) *\<^sub>u (G b)\<close>
  using assms compatible_def lvalue_pair_apply by blast

lemma lvalue_pair_apply':
  assumes \<open>compatible F G\<close>
  shows \<open>(F; G) (a \<otimes>\<^sub>u b) = (G b) *\<^sub>u (F a)\<close>
  apply (subst lvalue_pair_apply)
  using assms by (auto simp: compatible_def intro: lvalue_hom)



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
  assumes "compatible A B" and [simp]: \<open>lvalue C\<close> and [simp]: \<open>lvalue D\<close>
  shows "(A; B) o (C \<otimes>\<^sub>h D) = (A o C; B o D)"
  apply (rule tensor_extensionality)
  using assms by (simp_all add: tensor_update_hom_is_hom lvalue_pair_apply comp_update_hom)

lemma compatible_tensor_id_update_left[simp]:
  fixes F :: "'a::domain update \<Rightarrow> 'c::domain update" and G :: "'b::domain update \<Rightarrow> 'c::domain update"
  assumes "compatible F G"
  shows "compatible (\<lambda>a. id_update \<otimes>\<^sub>u F a) (\<lambda>a. id_update \<otimes>\<^sub>u G a)"
  using assms apply (rule compatible_comp_inner[unfolded o_def])
  by simp
  
lemma compatible_tensor_id_update_right[simp]:
  fixes F :: "'a::domain update \<Rightarrow> 'c::domain update" and G :: "'b::domain update \<Rightarrow> 'c::domain update"
  assumes "compatible F G"
  shows "compatible (\<lambda>a. F a \<otimes>\<^sub>u id_update) (\<lambda>a. G a \<otimes>\<^sub>u id_update)"
  using assms apply (rule compatible_comp_inner[unfolded o_def])
  by simp

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

lemma lvalue_comp_pair:
  assumes [simp]: \<open>lvalue F\<close> and [simp]: \<open>compatible G H\<close>
  shows "(F o G; F o H) = F o (G; H)"
proof (rule tensor_extensionality)
  show \<open>update_hom (F \<circ> G;F \<circ> H)\<close> and \<open>update_hom (F \<circ> (G;H))\<close>
    by simp_all

  have [simp]: \<open>compatible (F o G) (F o H)\<close>
    apply (rule compatible_comp_inner, simp)
    by simp
  then have [simp]: \<open>lvalue (F \<circ> G)\<close> \<open>lvalue (F \<circ> H)\<close>
    unfolding compatible_def by auto
  from assms have [simp]: \<open>lvalue G\<close> \<open>lvalue H\<close>
    unfolding compatible_def by auto
  fix a b
  show \<open>(F \<circ> G;F \<circ> H) (a \<otimes>\<^sub>u b) = (F \<circ> (G;H)) (a \<otimes>\<^sub>u b)\<close>
    by (auto simp: lvalue_pair_apply lvalue_mult tensor_update_mult)
qed

subsection \<open>Fst and Snd\<close>

definition Fst where \<open>Fst a = a \<otimes>\<^sub>u id_update\<close>
definition Snd where \<open>Snd a = id_update \<otimes>\<^sub>u a\<close>

lemma lvalue_Fst[simp]: \<open>lvalue Fst\<close>
  unfolding Fst_def by (rule lvalue_tensor_left)

lemma lvalue_Snd[simp]: \<open>lvalue Snd\<close>
  unfolding Snd_def by (rule lvalue_tensor_right)

lemma compatible_Fst_Snd[simp]: \<open>compatible Fst Snd\<close>
  apply (rule compatibleI, simp, simp)
  by (simp add: Fst_def Snd_def tensor_update_mult)

lemmas compatible_Snd_Fst[simp] = compatible_Fst_Snd[THEN compatible_sym]

definition \<open>swap = (Snd; Fst)\<close>

lemma swap_apply[simp]: "swap (a \<otimes>\<^sub>u b) = (b \<otimes>\<^sub>u a)"
  unfolding swap_def
  by (simp add: Axioms.lvalue_pair_apply Fst_def Snd_def tensor_update_mult) 

lemma swap_o_Fst: "swap o Fst = Snd"
  by (auto simp add: Fst_def Snd_def)
lemma swap_o_Snd: "swap o Snd = Fst"
  by (auto simp add: Fst_def Snd_def)

lemma lvalue_swap[simp]: \<open>lvalue swap\<close>
  by (simp add: swap_def)

lemma pair_Fst_Snd: \<open>(Fst; Snd) = id\<close>
  apply (rule tensor_extensionality)
  by (simp_all add: lvalue_pair_apply Fst_def Snd_def tensor_update_mult)

(* lemma pair_Snd_Fst: \<open>(Snd; Fst) = swap\<close>
  apply (rule tensor_extensionality)
  by (simp_all add: lvalue_pair_apply Fst_def Snd_def tensor_update_mult) *)

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


lemma compatible3[simp]:
  assumes [simp]: "compatible F G" and "compatible G H" and "compatible F H"
  shows "compatible (F; G) H"
proof (rule compatibleI)
  have [simp]: \<open>lvalue F\<close> \<open>lvalue G\<close> \<open>lvalue H\<close>
    using assms compatible_def by auto
  then have [simp]: \<open>update_hom F\<close> \<open>update_hom G\<close> \<open>update_hom H\<close>
    using lvalue_hom by blast+
  have [simp]: \<open>update_hom (\<lambda>a. (F;G) a *\<^sub>u z)\<close> for z
    apply (rule comp_update_hom[unfolded o_def, of \<open>(F;G)\<close>])
    by simp_all
  have [simp]: \<open>update_hom (\<lambda>a. z *\<^sub>u (F;G) a)\<close> for z
    apply (rule comp_update_hom[unfolded o_def, of \<open>(F;G)\<close>])
    by simp_all
  have "(F; G) (f \<otimes>\<^sub>u g) *\<^sub>u H h = H h *\<^sub>u (F; G) (f \<otimes>\<^sub>u g)" for f g h
  proof -
    have FH: "F f *\<^sub>u H h = H h *\<^sub>u F f"
      using assms compatible_def by metis
    have GH: "G g *\<^sub>u H h = H h *\<^sub>u G g"
      using assms compatible_def by metis
    have \<open>(F; G) (f \<otimes>\<^sub>u g) *\<^sub>u (H h) = F f *\<^sub>u G g *\<^sub>u H h\<close>
      using \<open>compatible F G\<close> by (subst lvalue_pair_apply, auto)
    also have \<open>\<dots> = H h *\<^sub>u F f *\<^sub>u G g\<close>
      using FH GH by (metis comp_update_assoc)
    also have \<open>\<dots> = H h *\<^sub>u (F; G) (f \<otimes>\<^sub>u g)\<close>
      using \<open>compatible F G\<close> by (subst lvalue_pair_apply, auto simp: comp_update_assoc)
    finally show ?thesis
      by -
  qed
  then show "(F; G) fg *\<^sub>u (H h) = (H h) *\<^sub>u (F; G) fg" for fg h
    apply (rule_tac tensor_extensionality[THEN fun_cong])
    by auto
  show "lvalue H" and  "lvalue (F; G)"
    by simp_all
qed

lemma compatible3'[simp]:
  assumes "compatible F G" and "compatible G H" and "compatible F H"
  shows "compatible F (G; H)"
  apply (rule compatible_sym)
  apply (rule compatible3)
  using assms by (auto simp: compatible_sym)

lemma pair_o_swap[simp]:
  assumes [simp]: "compatible A B"
  shows "(A; B) o swap = (B; A)"
proof (rule tensor_extensionality)
  have [simp]: "update_hom A" "update_hom B"
    apply (metis (no_types, hide_lams) assms compatible_lvalue1 lvalue_hom)
    by (metis (full_types) assms compatible_lvalue2 lvalue_hom)
  then show \<open>update_hom ((A; B) \<circ> swap)\<close>
    by (simp add: assms lvalue_swap)
  show \<open>update_hom (B; A)\<close>
    by (metis (no_types, lifting) assms compatible_sym lvalue_hom pair_lvalue)
  show \<open>((A; B) \<circ> swap) (a \<otimes>\<^sub>u b) = (B; A) (a \<otimes>\<^sub>u b)\<close> for a b
    (* Without the "only:", we would not need the "apply subst",
       but that proof fails when instantiated in Classical.thy *)
    apply (simp only: o_def swap_apply)
    apply (subst lvalue_pair_apply, simp)
    apply (subst lvalue_pair_apply, simp add: compatible_sym)
    by (metis (no_types, lifting) assms compatible_def)
qed

subsection \<open>Associativity of the tensor product\<close>

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

lemma lvalue_assoc[simp]: \<open>lvalue assoc\<close>
  unfolding assoc_def
  by force

lemma lvalue_assoc'[simp]: \<open>lvalue assoc'\<close>
  unfolding assoc'_def 
  by force

lemma pair_o_assoc[simp]:
  assumes [simp]: \<open>compatible F G\<close> \<open>compatible G H\<close> \<open>compatible F H\<close>
  shows \<open>(F; (G; H)) \<circ> assoc = ((F; G); H)\<close>
proof (rule tensor_extensionality3')
  show \<open>lvalue ((F; (G; H)) \<circ> assoc)\<close>
    by simp
  show \<open>lvalue ((F; G); H)\<close>
    by simp
  show \<open>((F; (G; H)) \<circ> assoc) ((f \<otimes>\<^sub>u g) \<otimes>\<^sub>u h) = ((F; G); H) ((f \<otimes>\<^sub>u g) \<otimes>\<^sub>u h)\<close> for f g h
    by (simp add: lvalue_pair_apply assoc_apply comp_update_assoc)
qed

lemma pair_o_assoc'[simp]:
  assumes [simp]: \<open>compatible F G\<close> \<open>compatible G H\<close> \<open>compatible F H\<close>
  shows \<open>((F; G); H) \<circ> assoc' = (F; (G; H))\<close>
proof (rule tensor_extensionality3)
  show \<open>lvalue (((F; G); H) \<circ> assoc')\<close>
    by (simp add: lvalue_assoc')
  show \<open>lvalue (F; (G; H))\<close>
    by simp
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
