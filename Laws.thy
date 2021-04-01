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

subsection \<open>Tensor product of homs\<close>

definition tensor_update_hom  (infixr "\<otimes>\<^sub>h" 70) where
  "tensor_update_hom F G = tensor_lift (\<lambda>a b. F a \<otimes>\<^sub>u G b)" 

lemma tensor_update_hom_hom_is_2hom[simp]:
  assumes \<open>update_hom F\<close> and \<open>update_hom G\<close>
  shows \<open>update_2hom (\<lambda>a b. F a \<otimes>\<^sub>u G b)\<close>
  apply (rule update_2hom_o_hom_left_is_hom, rule update_2hom_o_hom_right_is_hom)
  by (rule tensor_update_is_2hom assms)+

lemma tensor_update_hom_is_hom: "update_hom F \<Longrightarrow> update_hom G \<Longrightarrow> update_hom (F \<otimes>\<^sub>h G)"
  unfolding tensor_update_hom_def apply (rule tensor_lift_hom) by simp

lemma tensor_update_hom_apply[simp]:
  assumes \<open>update_hom F\<close> and \<open>update_hom G\<close>
  shows "(F \<otimes>\<^sub>h G) (a \<otimes>\<^sub>u b) = F a \<otimes>\<^sub>u G b"
  unfolding tensor_update_hom_def 
  using tensor_lift_correct tensor_update_hom_hom_is_2hom[OF assms] 
  by metis

lemma update_hom_tensor_is_2hom[simp]: \<open>update_hom F \<Longrightarrow> update_2hom (\<lambda>a b. F (a \<otimes>\<^sub>u b))\<close>
  using tensor_update_is_2hom by (rule update_hom_o_2hom_is_2hom)

lemma update_hom_tensor_left_is_hom[simp]: "update_hom ((\<otimes>\<^sub>u) a :: 'b::domain update \<Rightarrow> _)" 
  for a :: "'a::domain update"
  apply (rule update_2hom_right_is_hom)
  by (simp add: update_2hom_right_is_hom)

lemma update_hom_tensor_right_is_hom[simp]: "update_hom (\<lambda>a::'a::domain update. (\<otimes>\<^sub>u) a b)"
  for b :: "'b::domain update"
  by (simp add: update_2hom_left_is_hom)

lemma tensor_extensionality3: 
  fixes F G :: \<open>('a::domain\<times>'b::domain\<times>'c::domain, 'd::domain) update_hom\<close>
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
  fixes F G :: \<open>(('a::domain\<times>'b::domain)\<times>'c::domain, 'd::domain) update_hom\<close>
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

definition compatible :: \<open>('a::domain,'c::domain) update_hom \<Rightarrow> ('b::domain,'c) update_hom \<Rightarrow> bool\<close> where
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

definition lvalue_pair :: \<open>('a::domain,'c::domain) update_hom \<Rightarrow> ('b::domain,'c) update_hom
         \<Rightarrow> ('a\<times>'b, 'c) update_hom\<close> ("'(_;_')") where
  \<open>(F; G) = tensor_lift (\<lambda>a b. F a *\<^sub>u G b)\<close>


(* lemma update_hom_F_comp_G1:
  assumes \<open>update_hom G\<close>
  shows \<open>update_hom (\<lambda>b. a *\<^sub>u G b)\<close>
  using assms apply (rule comp_update_hom[of G \<open>\<lambda>b. a *\<^sub>u b\<close>, unfolded comp_def])
  apply (rule update_2hom_right_is_hom) using comp_update_is_2hom by auto *)

(* lemma update_hom_F_comp_G2:
  assumes \<open>update_hom F\<close>
  shows \<open>update_hom (\<lambda>a. F a *\<^sub>u G b)\<close> 
  using assms apply (rule comp_update_hom[of F \<open>\<lambda>a. a *\<^sub>u G b\<close>, unfolded comp_def])
  apply (rule update_2hom_left_is_hom) using comp_update_is_2hom by auto *)

lemma update_2hom_F_comp_G[simp]: (* TODO: used? rename! *)
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
  using tensor_lift_correct update_2hom_F_comp_G[OF assms]
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


(* TODO: Use capital letters FGH not xyz *)
lemma compatible3[simp]:
  assumes [simp]: "compatible x y" and "compatible y z" and "compatible x z"
  shows "compatible (x; y) z"
proof (rule compatibleI)
  have [simp]: \<open>lvalue x\<close> \<open>lvalue y\<close> \<open>lvalue z\<close>
    using assms compatible_def by auto
  then have [simp]: \<open>update_hom x\<close> \<open>update_hom y\<close> \<open>update_hom z\<close>
    using lvalue_hom by blast+
  have "((x; y); z) ((f \<otimes>\<^sub>u g) \<otimes>\<^sub>u h) = (z; (x; y)) (h \<otimes>\<^sub>u (f \<otimes>\<^sub>u g))" for f g h
    using assms apply (simp add: lvalue_pair_apply compatible_def comp_update_assoc)
    by (metis comp_update_assoc)
  then have "(((x; y); z) \<circ> swap \<circ> (\<otimes>\<^sub>u) h) (f \<otimes>\<^sub>u g)
           = ((z; (x; y)) \<circ> (\<otimes>\<^sub>u) h) (f \<otimes>\<^sub>u g)" for f g h
    by auto
  then have *: "((x; y); z) \<circ> swap \<circ> (\<otimes>\<^sub>u) h = (z; (x; y)) \<circ> (\<otimes>\<^sub>u) h" for h
    apply (rule tensor_extensionality[rotated -1])
    by (intro comp_update_hom lvalue_pair_is_hom; simp)+
  have "((x; y); z) (fg \<otimes>\<^sub>u h) = (z; (x; y)) (h \<otimes>\<^sub>u fg)" for fg h
    using *
    using comp_eq_dest_lhs by fastforce
  then show "(x; y) fg *\<^sub>u (z h) = (z h) *\<^sub>u (x; y) fg" for fg h
    unfolding compatible_def by (simp add: lvalue_pair_apply)
  show "lvalue z" and  "lvalue (x; y)"
    by simp_all
qed

(* TODO: Use capital letters FGH not xyz *)
lemma compatible3'[simp]:
  assumes "compatible x y" and "compatible y z" and "compatible x z"
  shows "compatible x (y; z)"
  apply (rule compatible_sym)
  apply (rule compatible3)
  using assms by (auto simp: compatible_sym)

lemma compatible_comp_left[simp]: "compatible x y \<Longrightarrow> lvalue z \<Longrightarrow> compatible (x \<circ> z) y"
  by (simp add: compatible_def)

lemma compatible_comp_right[simp]: "compatible x y \<Longrightarrow> lvalue z \<Longrightarrow> compatible x (y \<circ> z)"
  by (simp add: compatible_def)

lemma compatible_comp_inner[simp]: 
  "compatible x y \<Longrightarrow> lvalue z \<Longrightarrow> compatible (z \<circ> x) (z \<circ> y)"
  by (smt (verit, best) comp_apply compatible_def lvalue_comp lvalue_mult)

lemma compatible_lvalue1: \<open>compatible x y \<Longrightarrow> lvalue x\<close>
  by (simp add: compatible_def)
lemma compatible_lvalue2: \<open>compatible x y \<Longrightarrow> lvalue y\<close>
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

section \<open>Associativity of the tensor product\<close>

definition assoc :: \<open>(('a::domain\<times>'b::domain)\<times>'c::domain, 'a\<times>('b\<times>'c)) update_hom\<close> where 
  \<open>assoc = ((Fst; Snd o Fst); Snd o Snd)\<close>

lemma assoc_is_hom[simp]: \<open>update_hom assoc\<close>
  by (auto simp: assoc_def)

lemma assoc_apply: \<open>assoc ((a \<otimes>\<^sub>u b) \<otimes>\<^sub>u c) = (a \<otimes>\<^sub>u (b \<otimes>\<^sub>u c))\<close>
  by (auto simp: assoc_def lvalue_pair_apply Fst_def Snd_def tensor_update_mult)

definition assoc' :: \<open>('a\<times>('b\<times>'c), ('a::domain\<times>'b::domain)\<times>'c::domain) update_hom\<close> where 
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
   variable compatibility facts. *)
simproc_setup "compatibility_warn" ("compatible x y") = \<open>fn m => fn ctxt => fn ct => let
  val (x,y) = case Thm.term_of ct of
                 Const(\<^const_name>\<open>compatible\<close>,_ ) $ x $ y => (x,y)
  val str : string lazy = Lazy.lazy (fn () => Syntax.string_of_term ctxt (Thm.term_of ct))
  fun w msg = warning (msg ^ "\n(Disable these warnings with: using [[simproc del: compatibility_warn]])")
  (* val _ = \<^print> (x,y) *)
  val _ = case (x,y) of (Free(n,T), Free(n',T')) => 
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
          | _ => w ("Simplification subgoal " ^ Lazy.force str ^ 
                    "\ncannot be reduced to a compatibility of two variables (such as \<open>compatibility x y\<close>).\n" ^
                    "Try adding a simplification rule that breaks it down (such as, e.g., " ^ @{fact compatible3} ^ ").")
  in NONE end\<close>


(* Abbreviations: "mutually f (x1,x2,x3,\<dots>)" expands to a conjunction
   of all "f xi xj" with i\<noteq>y.

   "each f (x1,x2,x3,\<dots>)" expands to a conjunction of all "f xi". *)

syntax "_mutually" :: "'a \<Rightarrow> args \<Rightarrow> 'b" ("mutually _ '(_')")
syntax "_mutually2" :: "'a \<Rightarrow> 'b \<Rightarrow> args \<Rightarrow> args \<Rightarrow> 'c"

translations "mutually f (x)" => "CONST True"
translations "mutually f (_args x y)" => "f x y \<and> f y x"
translations "mutually f (_args x (_args x' xs))" => "_mutually2 f x (_args x' xs) (_args x' xs)"
translations "_mutually2 f x y zs" => "f x y \<and> f y x \<and> _mutually f zs"
translations "_mutually2 f x (_args y ys) zs" => "f x y \<and> f y x \<and> _mutually2 f x ys zs"

syntax "_each" :: "'a \<Rightarrow> args \<Rightarrow> 'b" ("each _ '(_')")
translations "each f (x)" => "f x"
translations "_each f (_args x xs)" => "f x \<and> _each f xs"

(* Declares the attribute [compat]. If applied to a conjunction 
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


experiment begin
lemma 
  assumes [compatible]: "mutually compatible (a,b,c)"
  shows True
proof -
  have "lvalue b" by simp
  have "compatible b c" by simp
  have "compatible (a; b) c" by simp
  show ?thesis by simp
qed
end



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
