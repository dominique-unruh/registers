(* AXIOM INSTANTIATION (use instantiate_laws.py to generate Laws_Classical.thy)
 
   domain \<rightarrow> type *)

theory Axioms_Classical
  imports Main
begin

type_synonym 'a update = \<open>'a rel\<close>

abbreviation (input) comp_update :: "'a update \<Rightarrow> 'a update \<Rightarrow> 'a update" where
  "comp_update a b \<equiv> b O a"

abbreviation (input) id_update :: "'a update" where
  "id_update \<equiv> Id"

lemma id_update_left: "comp_update id_update a = a"
  by (rule R_O_Id)
lemma id_update_right: "comp_update a id_update = a"
  by (rule Id_O_R)

lemma comp_update_assoc: "comp_update (comp_update a b) c = comp_update a (comp_update b c)"
  by auto

type_synonym ('a,'b) update_hom = \<open>'a update \<Rightarrow> 'b update\<close>
definition update_hom :: \<open>('a,'b) update_hom \<Rightarrow> bool\<close> where
  \<open>update_hom F \<longleftrightarrow> (\<exists>R. F = Image R)\<close>

lemma id_update_hom: \<open>update_hom id\<close>
  unfolding update_hom_def
  by (metis Image_Id eq_id_iff)

definition rel_of_update_hom :: \<open>('a,'b) update_hom \<Rightarrow> (('a\<times>'a)\<times>('b\<times>'b)) set\<close> where
  \<open>rel_of_update_hom F = (SOME R. F = Image R)\<close>

lemma rel_of_update_hom: \<open>update_hom F \<Longrightarrow> F = Image (rel_of_update_hom F)\<close>
  unfolding update_hom_def rel_of_update_hom_def
  by (metis (mono_tags) someI_ex)

lemma update_hom_mono: "update_hom F \<Longrightarrow> mono F"
  by (auto simp: update_hom_def mono_def Image_def)

lemma comp_update_hom: "update_hom F \<Longrightarrow> update_hom G \<Longrightarrow> update_hom (G \<circ> F)"
  unfolding update_hom_def apply auto
  apply (rule_tac x=\<open>R O Ra\<close> in exI)
  by (auto simp: o_def)

lemma converse_hom: \<open>update_hom converse\<close>
  unfolding update_hom_def
  apply (rule exI[where x=\<open>{((x,y),(y,x))| x y. True}\<close>])
  by (auto simp: converse_def Image_def)

type_synonym ('a,'b,'c) update_2hom = \<open>'a update \<Rightarrow> 'b update \<Rightarrow> 'c update\<close>

definition update_2hom :: "('a, 'b, 'c) update_2hom \<Rightarrow> bool" where
  \<open>update_2hom F2 \<longleftrightarrow> (\<exists>R2. \<forall>a b. F2 a b = R2 `` (a \<times> b))\<close>

definition rel_of_update_2hom :: \<open>('a,'b,'c) update_2hom \<Rightarrow> ((('a\<times>'a) \<times> ('b\<times>'b)) \<times> ('c\<times>'c)) set\<close> where
  \<open>rel_of_update_2hom F2 = (SOME R2. \<forall>a b. F2 a b = R2 `` (a \<times> b))\<close>

lemma rel_of_update_2hom: \<open>update_2hom F2 \<Longrightarrow> F2 a b = rel_of_update_2hom F2 `` (a \<times> b)\<close>
  unfolding rel_of_update_2hom_def update_2hom_def
  apply (rule someI2_ex)
  by auto

definition rel_prod :: "('a*'b) set => ('c*'d) set => (('a*'c) * ('b*'d)) set" where
  "rel_prod a b = (\<lambda>((a,b),(c,d)). ((a,c),(b,d))) ` (a \<times> b)"

lemma tensor_update_mult: \<open>rel_prod a b O rel_prod c d = rel_prod (a O c) (b O d)\<close>
  apply (auto simp: rel_prod_def relcomp_def relcompp_apply case_prod_beta image_def
      simp flip: Collect_case_prod)
  by force


lemma rel_prod_converse: \<open>(rel_prod a b)\<inverse> = rel_prod (a\<inverse>) (b\<inverse>)\<close>
  apply (auto simp: rel_prod_def converse_unfold image_def case_prod_beta)
  by force

lemma rel_prod_Id[simp]: "rel_prod Id Id = Id"
  by (auto simp: rel_prod_def Id_def case_prod_beta image_def)

lemma update_hom_o_2hom_is_2hom: \<open>update_2hom F2 \<Longrightarrow> update_hom G \<Longrightarrow> update_2hom (\<lambda>a b. G (F2 a b))\<close>
  unfolding update_2hom_def update_hom_def apply auto 
  apply (rule_tac x=\<open>R2 O R\<close> in exI)
  by auto
lemma update_2hom_o_hom_left_is_hom: \<open>update_2hom F2 \<Longrightarrow> update_hom G \<Longrightarrow> update_2hom (\<lambda>a b. F2 (G a) b)\<close>
  unfolding update_2hom_def update_hom_def apply auto 
  apply (rule_tac x=\<open>rel_prod R Id O R2\<close> in exI)
  apply (auto simp: rel_prod_def case_prod_beta)
  apply fastforce by blast

lemma update_2hom_sym: \<open>update_2hom F2 \<Longrightarrow> update_2hom (\<lambda>a b. F2 b a)\<close> 
  unfolding update_2hom_def update_hom_def apply auto 
  apply (rule_tac x=\<open>(\<lambda>((a,b),c). ((b,a),c)) ` R2\<close> in exI)
  apply (auto simp: case_prod_beta Image_def)
  apply fastforce by blast

lemma update_2hom_left_is_hom: \<open>update_2hom F2 \<Longrightarrow> update_hom (\<lambda>a. F2 a b)\<close>
  unfolding update_2hom_def update_hom_def apply auto 
  apply (rule_tac x=\<open>{(a',c')| a' b' c'. ((a',b'),c') \<in> R2 \<and> b' \<in> b}\<close> in exI)
  by fastforce

lemma comp_update_is_2hom: "update_2hom comp_update"
  unfolding update_2hom_def
  apply (rule_tac x=\<open>{((a',b'),c')| a' b' c'. fst a' = snd b' \<and> fst c' = fst b' \<and> snd c' = snd a'}\<close> in exI)
  by auto


abbreviation (input) tensor_update :: \<open>'a update \<Rightarrow> 'b update \<Rightarrow> ('a\<times>'b) update\<close> where
  \<open>tensor_update \<equiv> rel_prod\<close>


lemma tensor_update_is_2hom: \<open>update_2hom tensor_update\<close> 
  unfolding update_2hom_def[abs_def]
  apply (rule exI[of _ \<open>{(((ax,ay),(bx,by)), ((ax,bx),(ay,by)))| ax ay bx by. True} :: ((('a \<times> 'a) \<times> 'b \<times> 'b) \<times> ('a \<times> 'b) \<times> 'a \<times> 'b) set\<close>])
  apply (auto simp: rel_prod_def image_def case_prod_beta)
  by force

definition tensor_lift :: \<open>('a, 'b, 'c) update_2hom
                            \<Rightarrow> (('a\<times>'b, 'c) update_hom)\<close>
  where "tensor_lift F2 ab = {(cx,cy)| cx cy ax ay bx by. ((ax,bx),(ay,by)) \<in> ab
             \<and> (((ax,ay), (bx,by)), (cx,cy)) \<in> rel_of_update_2hom F2}"

lemma tensor_lift_hom: 
  assumes "update_2hom F2"
  shows "update_hom (tensor_lift F2)"
proof -
  define R2 where "R2 = rel_of_update_2hom F2"
  from assms
  have R2: "F2 a b = R2 `` (a \<times> b)" for a b
    by (simp add: R2_def rel_of_update_2hom)
  define R where \<open>R = {(((ax, bx), (ay, by)), (cx, cy))| ax bx ay by cx cy. (((ax, ay), (bx, by)), (cx, cy)) \<in> R2}\<close>
  have \<open>tensor_lift F2 = (``) R\<close>
   unfolding tensor_lift_def R2_def[symmetric]
   using R_def by blast
  then show ?thesis
    unfolding update_hom_def by auto
qed

lemma tensor_lift_correct: 
  assumes \<open>update_2hom F2\<close>
  shows \<open>(\<lambda>a b. tensor_lift F2 (tensor_update a b)) = F2\<close>
proof (intro ext)
  fix a :: \<open>('a\<times>'a) set\<close> and b :: \<open>('b\<times>'b) set\<close>
  define R2 where \<open>R2 = rel_of_update_2hom F2\<close>
  then have F2R2: "F2 a b = R2 `` (a \<times> b)" for a b
    using rel_of_update_2hom assms by metis
  show \<open>tensor_lift F2 (rel_prod a b) = F2 a b\<close>
  proof (intro set_eqI, case_tac x, rename_tac x y, hypsubst, rule iffI)
    fix x y :: 'c
    assume "(x, y) \<in> F2 a b"
    then have xyR2: \<open>(x,y) \<in> R2 `` (a \<times> b)\<close>
      using F2R2 by auto
    then show \<open>(x, y) \<in> tensor_lift F2 (tensor_update a b)\<close>
      unfolding tensor_lift_def R2_def[symmetric]
      apply (auto simp: rel_prod_def case_prod_beta image_def)
      by (meson fst_eqD snd_eqD)
  next
    fix x y :: 'c
    assume \<open>(x, y) \<in> tensor_lift F2 (tensor_update a b)\<close>
    then have \<open>(x, y) \<in> R2 `` (a \<times> b)\<close>
      unfolding tensor_lift_def R2_def[symmetric]
      by (auto simp: rel_prod_def case_prod_beta image_def)
    then show \<open>(x, y) \<in> F2 a b\<close>
      using F2R2 by auto
  qed
qed

lemma tensor_extensionality:
  assumes \<open>update_hom F\<close>
  assumes \<open>update_hom G\<close>
  assumes \<open>\<And>a b. F (tensor_update a b) = G (tensor_update a b)\<close>
  shows "F = G"
proof -
  define RF RG where "RF = rel_of_update_hom F" and "RG = rel_of_update_hom G"
  then have RF: "F = Image RF" and RG: "G = Image RG"
    using rel_of_update_hom assms by auto
  with assms have RFRG: "RF `` tensor_update a b = RG `` tensor_update a b" for a b
    by auto
  have "RF = RG"
  proof (rule set_eqI)
    fix v :: \<open>(('a \<times> 'b) \<times> ('a \<times> 'b)) \<times> ('c \<times> 'c)\<close>
    obtain ax bx ay "by" c where v: "v = (((ax,bx),(ay,by)),c)"
      apply atomize_elim
      by (metis surj_pair)
    have \<open>v \<in> RF \<longleftrightarrow> (((ax,bx),(ay,by)),c) \<in> RF\<close>
      using v by simp
    also have \<open>\<dots> \<longleftrightarrow> c \<in> RF `` tensor_update {(ax,ay)} {(bx,by)}\<close>
      unfolding rel_prod_def by simp
    also have \<open>\<dots> \<longleftrightarrow> c \<in> RG `` tensor_update {(ax,ay)} {(bx,by)}\<close>
      by (simp add: RFRG)
    also have \<open>\<dots> \<longleftrightarrow> (((ax,bx),(ay,by)),c) \<in> RG\<close>
      unfolding rel_prod_def by simp
    also have \<open>\<dots> \<longleftrightarrow> v \<in> RG\<close>
      using v by simp
    finally show \<open>v \<in> RF \<longleftrightarrow> v \<in> RG\<close>
      by -
  qed
  then show \<open>F = G\<close>
    using RF RG by simp
qed

definition lvalue :: \<open>('a,'b) update_hom \<Rightarrow> bool\<close> where
  \<open>lvalue F \<longleftrightarrow> update_hom F \<and> (\<forall>a a'. F a O F a' = F (a O a')) \<and> F Id = Id \<and> (\<forall>a. F (a\<inverse>) = (F a)\<inverse>)\<close>

lemma lvalue_of_id: \<open>lvalue F \<Longrightarrow> F id_update = id_update\<close>
  by (simp add: lvalue_def)

lemma update_hom_tensor_left: \<open>update_hom (\<lambda>a. tensor_update a id_update)\<close>
  unfolding update_hom_def apply (rule exI[of _ \<open>{((a1,a2),((a1,b),(a2,b)))| a1 a2 b. True}\<close>])
  apply (auto intro!: ext simp: Image_def[abs_def] rel_prod_def case_prod_beta image_def Id_def)
  by (metis fst_conv snd_conv)
lemma update_hom_tensor_right: \<open>update_hom (\<lambda>a. tensor_update id_update a)\<close>
  unfolding update_hom_def apply (rule exI[of _ \<open>{((a1,a2),((b,a1),(b,a2)))| a1 a2 b. True}\<close>])
  apply (auto intro!: ext simp: Image_def[abs_def] rel_prod_def case_prod_beta image_def Id_def)
  by (metis fst_conv snd_conv)

lemma lvalue_tensor_left: \<open>lvalue (\<lambda>a. tensor_update a id_update)\<close>
  apply (simp add: lvalue_def update_hom_tensor_left)
  apply (auto simp: rel_prod_def case_prod_beta relcomp_def relcompp_apply image_def)
  apply (metis fst_conv pair_in_Id_conv prod.exhaust_sel)
  apply (metis IdI fst_conv snd_conv)
  apply (metis IdI fst_conv snd_conv)
  by (metis IdI converse_iff fst_swap snd_conv swap_simp)

lemma lvalue_tensor_right: \<open>lvalue (\<lambda>a. tensor_update id_update a)\<close>
  apply (simp add: lvalue_def update_hom_tensor_right)
  apply (auto simp: rel_prod_def case_prod_beta relcomp_def relcompp_apply image_def)
  apply blast
  apply (metis IdI fst_conv snd_conv)
  apply (metis IdI fst_conv snd_eqD)
  apply (metis IdI fst_conv snd_conv)
  by (metis IdI converse_iff fst_conv snd_conv)


lemma
  lvalue_hom: "lvalue F \<Longrightarrow> update_hom F"
  by (simp add: lvalue_def) 

lemma
  lvalue_comp: "lvalue F \<Longrightarrow> lvalue G \<Longrightarrow> lvalue (G \<circ> F)"  
  for F :: "('a,'b) update_hom" and G :: "('b,'c) update_hom"
  by (simp add: comp_update_hom lvalue_def) 

lemma
  lvalue_mult: "lvalue F \<Longrightarrow> comp_update (F a) (F b) = F (comp_update a b)"
  by (simp add: lvalue_def)

lemma pair_lvalue_axiom: 
  assumes \<open>lvalue F\<close>
  assumes \<open>lvalue G\<close>
  assumes [simp]: \<open>update_hom p\<close>
  assumes compat: \<open>\<And>a b. comp_update (F a) (G b) = comp_update (G b) (F a)\<close>
  assumes ptensor: \<open>\<And>a b. p (tensor_update a b) = comp_update (F a) (G b)\<close>
  shows \<open>lvalue p\<close>
proof (unfold lvalue_def, intro conjI allI)
  from assms show \<open>update_hom p\<close> by -
  have h1: \<open>update_hom (\<lambda>a. p a O p a')\<close> for a'
    apply (rule update_2hom_left_is_hom)
    apply (rule update_2hom_o_hom_left_is_hom)
    using comp_update_is_2hom update_2hom_sym by auto
  have h2: \<open>update_hom (\<lambda>a. p (a O a'))\<close> for a'
    apply (rule update_2hom_left_is_hom)
    apply (rule update_hom_o_2hom_is_2hom[where G=p])
    using comp_update_is_2hom update_2hom_sym by auto
  have h3: \<open>update_hom (\<lambda>a'. p a O p a')\<close> for a
    apply (rule update_2hom_left_is_hom)
    apply (rule update_2hom_o_hom_left_is_hom)
    using comp_update_is_2hom update_2hom_sym by auto
  have h4: \<open>update_hom (\<lambda>a'. p (a O a'))\<close> for a
    apply (rule update_2hom_left_is_hom)
    apply (rule update_hom_o_2hom_is_2hom[where G=p])
    using comp_update_is_2hom update_2hom_sym by auto
  have h5: \<open>update_hom (\<lambda>a. p (a\<inverse>))\<close>
    apply (rule comp_update_hom[where G=p, unfolded o_def])
    by (simp_all add: converse_hom)
  have h6: \<open>update_hom (\<lambda>a. (p a)\<inverse>)\<close>
    apply (rule comp_update_hom[where F=p, unfolded o_def])
    by (simp_all add: converse_hom)
  have \<open>p (tensor_update a1 a2) O p (tensor_update a1' a2') = p ((tensor_update a1 a2) O (tensor_update a1' a2'))\<close> for a1 a2 a1' a2'
    unfolding ptensor tensor_update_mult
    by (metis assms(1) assms(2) comp_update_assoc lvalue_mult compat) 
  
  then have \<open>p (tensor_update a1 a2) O p a' = p ((tensor_update a1 a2) O a')\<close> for a1 a2 a'
    by (rule tensor_extensionality[OF h3 h4, THEN fun_cong])
  then show \<open>p a O p a' = p (a O a')\<close> for a a'
    by (rule tensor_extensionality[OF h1 h2, THEN fun_cong])

  show \<open>p Id = Id\<close>
    apply (simp flip: rel_prod_Id add: ptensor)
    by (metis R_O_Id assms(1) assms(2) lvalue_def)
  
  have \<open>p ((tensor_update a1 a2)\<inverse>) = (p (tensor_update a1 a2))\<inverse>\<close> for a1 a2
    apply (simp add: ptensor converse_relcomp rel_prod_converse)
    apply (subst compat)
    by (metis assms(1) assms(2) lvalue_def)

  then show \<open>p (a\<inverse>) = (p a)\<inverse>\<close> for a
    by (rule tensor_extensionality[OF h5 h6, THEN fun_cong])
qed

end
