section \<open>Classical instantiation of registerss\<close>

(* AXIOM INSTANTIATION (use instantiate_laws.py to generate Laws_Classical.thy)
 
   domain \<rightarrow> type

   Generic laws about registers \<rightarrow> Generic laws about registers, instantiated classically
*)

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

type_synonym ('a,'b) preregister = \<open>'a update \<Rightarrow> 'b update\<close>
definition preregister :: \<open>('a,'b) preregister \<Rightarrow> bool\<close> where
  \<open>preregister F \<longleftrightarrow> (\<exists>R. F = Image R)\<close>

lemma id_preregister: \<open>preregister id\<close>
  unfolding preregister_def
  by (metis Image_Id eq_id_iff)

lemma preregister_mult_right: \<open>preregister (\<lambda>a. comp_update a z)\<close>
  unfolding preregister_def 
  apply (rule exI[of _ \<open>{((a,b),(c,b))| a b c. (c,a) \<in> z}\<close>])
  by (auto intro!:ext simp: relcomp_def relcompp_apply Image_def[abs_def])

lemma preregister_mult_left: \<open>preregister (\<lambda>a. comp_update z a)\<close>
  unfolding preregister_def 
  apply (rule exI[of _ \<open>{((a,b),(a,d))| a b c d. (b,d) \<in> z}\<close>])
  by (auto intro!:ext simp: relcomp_def relcompp_apply Image_def[abs_def])

definition rel_of_preregister :: \<open>('a,'b) preregister \<Rightarrow> (('a\<times>'a)\<times>('b\<times>'b)) set\<close> where
  \<open>rel_of_preregister F = (SOME R. F = Image R)\<close>

lemma rel_of_preregister: \<open>preregister F \<Longrightarrow> F = Image (rel_of_preregister F)\<close>
  unfolding preregister_def rel_of_preregister_def
  by (metis (mono_tags) someI_ex)

lemma preregister_mono: "preregister F \<Longrightarrow> mono F"
  by (auto simp: preregister_def mono_def Image_def)

lemma comp_preregister: "preregister F \<Longrightarrow> preregister G \<Longrightarrow> preregister (G \<circ> F)"
  unfolding preregister_def apply auto
  apply (rule_tac x=\<open>R O Ra\<close> in exI)
  by (auto simp: o_def)

lemma converse_preregister: \<open>preregister converse\<close>
  unfolding preregister_def
  apply (rule exI[where x=\<open>{((x,y),(y,x))| x y. True}\<close>])
  by (auto simp: converse_def Image_def)

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

abbreviation (input) tensor_update :: \<open>'a update \<Rightarrow> 'b update \<Rightarrow> ('a\<times>'b) update\<close> where
  \<open>tensor_update \<equiv> rel_prod\<close>

lemma tensor_extensionality:
  assumes \<open>preregister F\<close>
  assumes \<open>preregister G\<close>
  assumes \<open>\<And>a b. F (tensor_update a b) = G (tensor_update a b)\<close>
  shows "F = G"
proof -
  define RF RG where "RF = rel_of_preregister F" and "RG = rel_of_preregister G"
  then have RF: "F = Image RF" and RG: "G = Image RG"
    using rel_of_preregister assms by auto
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

definition register :: \<open>('a,'b) preregister \<Rightarrow> bool\<close> where
  \<open>register F \<longleftrightarrow> preregister F \<and> (\<forall>a a'. F a O F a' = F (a O a')) \<and> F Id = Id \<and> (\<forall>a. F (a\<inverse>) = (F a)\<inverse>)\<close>

lemma register_id: \<open>register F \<Longrightarrow> F id_update = id_update\<close>
  by (simp add: register_def)

(* lemma preregister_tensor_left: \<open>preregister (\<lambda>a. tensor_update a b)\<close>
  unfolding preregister_def apply (rule exI[of _ \<open>{((a1,a2),((a1,b1),(a2,b2)))| a1 a2 b1 b2. (b1,b2) \<in> b}\<close>])
  apply (auto intro!: ext simp: Image_def[abs_def] rel_prod_def case_prod_beta image_def Id_def)
  by (metis fst_conv snd_conv)
lemma preregister_tensor_right: \<open>preregister (\<lambda>a. tensor_update b a)\<close>
  unfolding preregister_def apply (rule exI[of _ \<open>{((a1,a2),((b1,a1),(b2,a2)))| a1 a2 b1 b2. (b1,b2) \<in> b}\<close>])
  apply (auto intro!: ext simp: Image_def[abs_def] rel_prod_def case_prod_beta image_def Id_def)
  by (metis fst_conv snd_conv) *)

lemma register_tensor_left: \<open>register (\<lambda>a. tensor_update a id_update)\<close>
  apply (auto simp: register_def preregister_def)
    apply (rule exI[of _ \<open>{((a1,a2),((a1,b),(a2,b)))| a1 a2 b. True}\<close>])
      apply (auto intro!: ext simp: Image_def[abs_def] rel_prod_def case_prod_beta image_def Id_def 
                  relcompp_apply relcomp_def converse_def)
  by (metis fst_conv snd_conv)+

lemma register_tensor_right: \<open>register (\<lambda>a. tensor_update id_update a)\<close>
  apply (auto simp: register_def preregister_def)
    apply (rule exI[of _ \<open>{((b1,b2),((a,b1),(a,b2)))| a b1 b2. True}\<close>])
      apply (auto intro!: ext simp: Image_def[abs_def] rel_prod_def case_prod_beta image_def Id_def 
                  relcompp_apply relcomp_def converse_def)
  by (metis fst_conv snd_conv)+

lemma
  register_preregister: "register F \<Longrightarrow> preregister F"
  by (simp add: register_def) 

lemma
  register_comp: "register F \<Longrightarrow> register G \<Longrightarrow> register (G \<circ> F)"  
  for F :: "('a,'b) preregister" and G :: "('b,'c) preregister"
  by (simp add: comp_preregister register_def) 

lemma
  register_mult: "register F \<Longrightarrow> comp_update (F a) (F b) = F (comp_update a b)"
  by (simp add: register_def)

definition register_pair ::
  \<open>('a update \<Rightarrow> 'c update) \<Rightarrow> ('b update \<Rightarrow> 'c update) \<Rightarrow> (('a\<times>'b) update \<Rightarrow> 'c update)\<close> where
  \<open>register_pair F G = Image {(((x1,y1),(x2,y2)),(m1,m3)) | x1 x2 y1 y2 m1 m2 m3.
      ((x1,x2),(m2,m3)) \<in> rel_of_preregister F \<and> ((y1,y2),(m1,m2)) \<in> rel_of_preregister G}\<close>

lemma register_pair_apply:
  assumes [simp]: \<open>register F\<close> \<open>register G\<close>
  assumes \<open>\<And>a b. comp_update (F a) (G b) = comp_update (G b) (F a)\<close>
  shows \<open>(register_pair F G) (tensor_update a b) = comp_update (F a) (G b)\<close>
proof -
  have [simp]: \<open>F a = rel_of_preregister F `` a\<close>
    by (metis assms(1) register_preregister rel_of_preregister)
  have [simp]: \<open>G b = rel_of_preregister G `` b\<close>
    by (metis assms(2) register_preregister rel_of_preregister)

  show ?thesis
    unfolding register_pair_def 
    apply (auto simp: relcomp_unfold rel_prod_def Image_def case_prod_beta)
    by blast
qed

lemma register_pair_is_register:
  fixes F :: \<open>'a update \<Rightarrow> 'c update\<close> and G
  assumes [simp]: \<open>register F\<close> and [simp]: \<open>register G\<close>
  assumes compat: \<open>\<And>a b. comp_update (F a) (G b) = comp_update (G b) (F a)\<close>
  shows \<open>register (register_pair F G)\<close> 
proof (unfold register_def, intro conjI allI)
  define p where \<open>p = (register_pair F G)\<close>
  
  show [simp]: \<open>preregister p\<close>
    unfolding p_def register_pair_def preregister_def by auto
  
  have ptensor: \<open>\<And>a b. p (tensor_update a b) = comp_update (F a) (G b)\<close>
    unfolding p_def
    using assms by (rule register_pair_apply)

  have h1: \<open>preregister (\<lambda>a. p a O p a')\<close> for a'
    apply (rule comp_preregister[where F=p, unfolded o_def])
    by (simp_all add: preregister_mult_left)
  have h2: \<open>preregister (\<lambda>a. p (a O a'))\<close> for a'
    apply (rule comp_preregister[where G=p, unfolded o_def])
    by (simp_all add: preregister_mult_left)
  have h3: \<open>preregister (\<lambda>a'. p a O p a')\<close> for a
    apply (rule comp_preregister[where F=p, unfolded o_def])
    by (simp_all add: preregister_mult_right)
  have h4: \<open>preregister (\<lambda>a'. p (a O a'))\<close> for a
    apply (rule comp_preregister[where G=p, unfolded o_def])
    by (simp_all add: preregister_mult_right)
  have h5: \<open>preregister (\<lambda>a. p (a\<inverse>))\<close>
    apply (rule comp_preregister[where G=p, unfolded o_def])
    by (simp_all add: converse_preregister)
  have h6: \<open>preregister (\<lambda>a. (p a)\<inverse>)\<close>
    apply (rule comp_preregister[where F=p, unfolded o_def])
    by (simp_all add: converse_preregister)

  have \<open>p (tensor_update a1 a2) O p (tensor_update a1' a2') = p ((tensor_update a1 a2) O (tensor_update a1' a2'))\<close> for a1 a2 a1' a2'
    unfolding ptensor tensor_update_mult
    by (metis assms(1) assms(2) comp_update_assoc register_mult compat) 
  
  then have \<open>p (tensor_update a1 a2) O p a' = p ((tensor_update a1 a2) O a')\<close> for a1 a2 a'
    by (rule tensor_extensionality[OF h3 h4, THEN fun_cong])

  then show \<open>p a O p a' = p (a O a')\<close> for a a'
    by (rule tensor_extensionality[OF h1 h2, THEN fun_cong])

  show \<open>p Id = Id\<close>
    apply (simp flip: rel_prod_Id add: ptensor)
    by (metis R_O_Id assms(1) assms(2) register_def)
  
  have \<open>p ((tensor_update a1 a2)\<inverse>) = (p (tensor_update a1 a2))\<inverse>\<close> for a1 a2
    apply (simp add: ptensor converse_relcomp rel_prod_converse)
    apply (subst compat)
    by (metis assms(1) assms(2) register_def)

  then show \<open>p (a\<inverse>) = (p a)\<inverse>\<close> for a
    by (rule tensor_extensionality[OF h5 h6, THEN fun_cong])
qed


end
