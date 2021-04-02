theory AxiomsAdj
imports Axioms
begin

axiomatization upd_adjoint :: "('a::domain, 'b::domain) update_nonsquare \<Rightarrow> ('b, 'a) update_nonsquare"

axiomatization where upd_adjoint_id: "upd_adjoint id_update = id_update"
axiomatization where upd_adjoint_involution: "upd_adjoint (upd_adjoint a) = a"
axiomatization where upd_adjoint_comp: "upd_adjoint (comp_update a b) = comp_update (upd_adjoint b) (upd_adjoint a)"

definition unitary_update where \<open>unitary_update a \<longleftrightarrow> comp_update (upd_adjoint a) a = id_update \<and>
    comp_update a (upd_adjoint a) = id_update\<close>

definition sandwich where "sandwich a b = comp_update (comp_update a b) (upd_adjoint a)"

(* Instantiations of this axiom may use less premises or put the premises in a different order *)
axiomatization where lvalue_sandwhich_axiom:
  \<open>\<lbrakk>unitary_update a;
    update_hom (sandwich a);
    sandwich a id_update = id_update;
    \<And>x y. sandwich a (comp_update x y) = comp_update (sandwich a x) (sandwich a y);
    \<And>x. sandwich a (upd_adjoint x) = upd_adjoint (sandwich a x)\<rbrakk>
   \<Longrightarrow> lvalue (sandwich a)\<close>
for a :: \<open>('a::domain, 'b::domain) update_nonsquare\<close>

end
