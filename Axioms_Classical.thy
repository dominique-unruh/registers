section \<open>Classical instantiation of registerss\<close>

(* AXIOM INSTANTIATION (use instantiate_laws.py to generate Laws_Classical.thy)
 
   domain \<rightarrow> type

   Generic laws about registers \<rightarrow> Generic laws about registers, instantiated classically
*)

theory Axioms_Classical
  imports Main HOL.Map
begin

type_synonym 'a update = \<open>'a \<rightharpoonup> 'a\<close>

typ \<open>int update\<close>

(* TODO: direct instantiation *)
abbreviation (input) comp_update :: "'a update \<Rightarrow> 'a update \<Rightarrow> 'a update" where
  "comp_update a b \<equiv> a \<circ>\<^sub>m b"

abbreviation (input) id_update :: "'a update" where
  "id_update \<equiv> Some"

lemma id_update_left: "comp_update id_update a = a"
  by (auto intro!: ext simp add: map_comp_def option.case_eq_if)
lemma id_update_right: "comp_update a id_update = a"
  by auto

lemma comp_update_assoc: "comp_update (comp_update a b) c = comp_update a (comp_update b c)"
  by (auto intro!: ext simp add: map_comp_def option.case_eq_if)

type_synonym ('a,'b) preregister = \<open>'a update \<Rightarrow> 'b update\<close>
definition preregister :: \<open>('a,'b) preregister \<Rightarrow> bool\<close> where
  \<open>preregister F \<longleftrightarrow> (\<exists>g s. \<forall>a m. F a m = (case a (g m) of None \<Rightarrow> None | Some x \<Rightarrow> s x m))\<close>

lemma id_preregister: \<open>preregister id\<close>
  unfolding preregister_def
  apply (rule exI[of _ \<open>\<lambda>m. m\<close>])
  apply (rule exI[of _ \<open>\<lambda>a m. Some a\<close>])
  by (simp add: option.case_eq_if)

lemma preregister_mult_right: \<open>preregister (\<lambda>a. comp_update a z)\<close>
  unfolding preregister_def 
  apply (rule exI[of _ \<open>\<lambda>m. the (z m)\<close>])
  apply (rule exI[of _ \<open>\<lambda>x m. case z m of None \<Rightarrow> None | _ \<Rightarrow> Some x\<close>])
  by (auto simp add: option.case_eq_if)

lemma preregister_mult_left: \<open>preregister (\<lambda>a. comp_update z a)\<close>
  unfolding preregister_def 
  apply (rule exI[of _ \<open>\<lambda>m. m\<close>])
  apply (rule exI[of _ \<open>\<lambda>x m. z x\<close>])
  by (auto simp add: option.case_eq_if)

lemma comp_preregister: "preregister (G \<circ> F)" if "preregister F" and \<open>preregister G\<close>
proof -
  from \<open>preregister F\<close>
  obtain sF gF where F: \<open>F a m = (case a (gF m) of None \<Rightarrow> None | Some x \<Rightarrow> sF x m)\<close> for a m
    using preregister_def by blast
  from \<open>preregister G\<close>
  obtain sG gG where G: \<open>G a m = (case a (gG m) of None \<Rightarrow> None | Some x \<Rightarrow> sG x m)\<close> for a m
    using preregister_def by blast
  define s g where \<open>s a m = (case sF a (gG m) of None \<Rightarrow> None | Some x \<Rightarrow> sG x m)\<close>
    and \<open>g m = gF (gG m)\<close> for a m
  have \<open>(G \<circ> F) a m = (case a (g m) of None \<Rightarrow> None | Some x \<Rightarrow> s x m)\<close> for a m
    unfolding F G s_def g_def
    by (auto simp add: option.case_eq_if)
  then show "preregister (G \<circ> F)"
    using preregister_def by blast
qed

definition rel_prod :: "('a*'b) set => ('c*'d) set => (('a*'c) * ('b*'d)) set" where
  "rel_prod a b = (\<lambda>((a,b),(c,d)). ((a,c),(b,d))) ` (a \<times> b)"

definition tensor_update :: \<open>'a update \<Rightarrow> 'b update \<Rightarrow> ('a\<times>'b) update\<close> where
  \<open>tensor_update a b m = (case a (fst m) of None \<Rightarrow> None | Some x \<Rightarrow> (case b (snd m) of None \<Rightarrow> None | Some y \<Rightarrow> Some (x,y)))\<close>

lemma tensor_update_mult: \<open>comp_update (tensor_update a c) (tensor_update b d) = tensor_update (comp_update a b) (comp_update c d)\<close>
  by (auto intro!: ext simp add: map_comp_def option.case_eq_if tensor_update_def)

lemma tensor_extensionality:
  assumes \<open>preregister F\<close>
  assumes \<open>preregister G\<close>
  assumes \<open>\<And>a b. F (tensor_update a b) = G (tensor_update a b)\<close>
  shows "F = G"
  sorry (* TODO *)
(* proof -
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
qed *)

definition "valid_getter_setter g s \<longleftrightarrow> 
  (\<forall>b. b = s (g b) b) \<and> (\<forall>a b. g (s a b) = a) \<and> (\<forall>a a' b. s a (s a' b) = s a b)"

definition \<open>register_from_getter_setter g s a m = (case a (g m) of None \<Rightarrow> None | Some x \<Rightarrow> Some (s x m))\<close>
definition \<open>register_apply F a = the o F (Some o a)\<close>
definition \<open>getter_setter F = (let s = (\<lambda>a. register_apply F (\<lambda>_. a)) in ((\<lambda>m. THE x. s x m = m), s))\<close> for F :: \<open>'a update \<Rightarrow> 'b update\<close>

definition register :: \<open>('a,'b) preregister \<Rightarrow> bool\<close> where
  \<open>register F \<longleftrightarrow> (\<exists>g s. F = register_from_getter_setter g s \<and> valid_getter_setter g s)\<close>

lemma register_id: \<open>register F \<Longrightarrow> F id_update = id_update\<close>
  by (auto simp add: register_def valid_getter_setter_def register_from_getter_setter_def)

lemma register_tensor_left: \<open>register (\<lambda>a. tensor_update a id_update)\<close>
  apply (auto simp: register_def)
  apply (rule exI[of _ fst])
  apply (rule exI[of _ \<open>\<lambda>x' (x,y). (x',y)\<close>])
  by (auto intro!: ext simp add: tensor_update_def valid_getter_setter_def register_from_getter_setter_def option.case_eq_if)

lemma register_tensor_right: \<open>register (\<lambda>a. tensor_update id_update a)\<close>
  apply (auto simp: register_def)
  apply (rule exI[of _ snd])
  apply (rule exI[of _ \<open>\<lambda>y' (x,y). (x,y')\<close>])
  by (auto intro!: ext simp add: tensor_update_def valid_getter_setter_def register_from_getter_setter_def option.case_eq_if)

lemma register_preregister: "preregister F" if \<open>register F\<close>
proof -
  from \<open>register F\<close>
  obtain s g where F: \<open>F a m = (case a (g m) of None \<Rightarrow> None | Some x \<Rightarrow> Some (s x m))\<close> for a m
    unfolding register_from_getter_setter_def register_def by blast
  show ?thesis
    unfolding preregister_def
    apply (rule exI[of _ g])
    apply (rule exI[of _ \<open>\<lambda>x m. Some (s x m)\<close>])
    using F by simp
qed

lemma register_comp: "register (G \<circ> F)" if \<open>register F\<close> and \<open>register G\<close>
  for F :: "('a,'b) preregister" and G :: "('b,'c) preregister"
proof -
  from \<open>register F\<close>
  obtain sF gF where F: \<open>F a m = (case a (gF m) of None \<Rightarrow> None | Some x \<Rightarrow> Some (sF x m))\<close>
    and validF: \<open>valid_getter_setter gF sF\<close> for a m
    unfolding register_def register_from_getter_setter_def by blast
  from \<open>register G\<close>
  obtain sG gG where G: \<open>G a m = (case a (gG m) of None \<Rightarrow> None | Some x \<Rightarrow> Some (sG x m))\<close>
    and validG: \<open>valid_getter_setter gG sG\<close> for a m
    unfolding register_def register_from_getter_setter_def by blast
  define s g where \<open>s a m = sG (sF a (gG m)) m\<close> and \<open>g m = gF (gG m)\<close> for a m
  have \<open>(G \<circ> F) a m = (case a (g m) of None \<Rightarrow> None | Some x \<Rightarrow> Some (s x m))\<close> for a m
    by (auto simp add: option.case_eq_if F G s_def g_def)
  moreover have \<open>valid_getter_setter g s\<close>
    using validF validG by (auto simp: valid_getter_setter_def s_def g_def)
  ultimately show "register (G \<circ> F)"
    unfolding register_def register_from_getter_setter_def by blast
qed

lemma register_mult: "register F \<Longrightarrow> comp_update (F a) (F b) = F (comp_update a b)"
  by (auto intro!: ext simp: register_def register_from_getter_setter_def[abs_def] valid_getter_setter_def map_comp_def option.case_eq_if)

definition register_pair ::
  \<open>('a update \<Rightarrow> 'c update) \<Rightarrow> ('b update \<Rightarrow> 'c update) \<Rightarrow> (('a\<times>'b) update \<Rightarrow> 'c update)\<close> where
  \<open>register_pair F G = (let (gF, sF) = getter_setter F; (gG, sG) = getter_setter G in
    register_from_getter_setter (\<lambda>m. (gF m, gG m)) (\<lambda>(a,b) m. sF a (sG b m)))\<close>

lemma register_pair_apply:
  assumes [simp]: \<open>register F\<close> \<open>register G\<close>
  assumes \<open>\<And>a b. comp_update (F a) (G b) = comp_update (G b) (F a)\<close>
  shows \<open>(register_pair F G) (tensor_update a b) = comp_update (F a) (G b)\<close>
proof -
  obtain gF sF gG sG where gsF: \<open>(gF, sF) = getter_setter F\<close> and gsG: \<open>(gG, sG) = getter_setter G\<close>
    by (metis surj_pair)
  then have F: \<open>F = register_from_getter_setter gF sF\<close> and G: \<open>G = register_from_getter_setter gG sG\<close>
    sorry
  have FG: "register_pair F G = register_from_getter_setter (\<lambda>m. (gF m, gG m)) (\<lambda>(a, b) m. sF a (sG b m))"
    unfolding register_pair_def gsF[symmetric] gsG[symmetric] by auto
  show ?thesis
  proof (rule ext, rename_tac m)
    fix m
    consider (aNone) \<open>a (gF m) = None\<close> | (bNone) \<open>b (gG m) = None\<close>
      | (some) x y where \<open>a (gF m) = Some x\<close> and \<open>b (gG m) = Some y\<close>
      by auto
    then show \<open>register_pair F G (tensor_update a b) m = (F a \<circ>\<^sub>m G b) m\<close>
    proof cases
      case aNone
      then show ?thesis
        apply (subst (2) F, subst (2) G)
        apply (auto simp: register_pair_def gsF[symmetric] gsG[symmetric] tensor_update_def[abs_def]
                    case_prod_beta map_comp_def register_from_getter_setter_def[abs_def])
    next
      case bNone
      then show ?thesis sorry
    next
      case some
      then show ?thesis sorry
    qed
  qed
qed













    
    
    
    
    
    
    
    apply (subst (2) F, subst (2) G)
    unfolding 
    apply (auto intro!:ext simp: case_prod_beta register_pair_def gsF[symmetric] gsG[symmetric] 
                      register_from_getter_setter_def[abs_def] map_comp_def option.case_eq_if
                      tensor_update_def)
    apply (smt (verit, best) F G assms(3) map_comp_def option.case_eq_if option.distinct(1) option.sel register_from_getter_setter_def)

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
