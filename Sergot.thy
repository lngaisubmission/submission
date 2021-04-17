theory Sergot

imports Main HOL.Finite_Set

begin

typedecl i (*-- "type for possible worlds" *)
typedecl \<mu> (*-- "type for agents"      *)

abbreviation Ag :: "\<mu> set" ("Ag")
    where " Ag  \<equiv> (UNIV::\<mu> set)"
axiomatization where finiteActors: "finite Ag"

type_synonym \<sigma> = "(i\<Rightarrow>bool)"

abbreviation reflexive 
  where "reflexive R \<equiv>  (\<forall>x. R x x)"
abbreviation symmetric 
  where "symmetric R\<equiv> (\<forall>x y. R x y \<longrightarrow> R y  x)"
abbreviation transitive
  where "transitive R \<equiv> (\<forall>x y z. ((R x  y) \<and> (R y  z) \<longrightarrow> (R x z)))"
abbreviation eqrelation
  where "eqrelation R \<equiv> reflexive R \<and> symmetric R \<and> transitive R"

consts tilde :: "i\<Rightarrow>i\<Rightarrow>bool" (infixr "\<^bold>~" 70)    (*-- "accessibility relation ~"   *)
consts tildeAG :: "\<mu> \<Rightarrow> i\<Rightarrow>i\<Rightarrow>bool" ("~_")    (*-- "accessibility relation ~"   *)

axiomatization where xsub: "\<forall>(x::\<mu>). ((~ x) (\<tau>a::i)(\<tau>b::i) \<longrightarrow> ((\<tau>a::i)  \<^bold>~  (\<tau>b::i)))"
axiomatization where tildeeqU: "\<forall>x y. x \<^bold>~ y" (*DOES THIS CHANGE STUFF?*)
lemma tildeeq: "eqrelation tilde" using tildeeqU by simp
axiomatization where tildexeq: "\<forall>(x::\<mu>). eqrelation (~ x)"

abbreviation tildeG  :: "i\<Rightarrow> (\<mu> set)\<Rightarrow>i\<Rightarrow>bool" ("_ ~_  _")
  where "(\<tau>a ~ G \<tau>b)  \<equiv> (\<tau>a \<^bold>~ \<tau>b)  \<and> (\<forall>x. ((x \<in> G) \<longrightarrow>  (~ x) (\<tau>a::i) (\<tau>b::i)))" 
(*not using a set here for computational efficiency*)

abbreviation mtrue  :: "\<sigma>" ("\<^bold>\<top>")
  where "\<^bold>\<top> \<equiv> \<lambda>w. True" 
abbreviation mfalse :: "\<sigma>" ("\<^bold>\<bottom>") 
  where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"   
abbreviation mnot   :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_"[52]53)
  where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)"
abbreviation mand   :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<and>"51)
  where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<and>\<psi>(w)"   
abbreviation mor    :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<or>"50)
  where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<or>\<psi>(w)"   
abbreviation mimp   :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<rightarrow>"49) 
  where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longrightarrow>\<psi>(w)"  
abbreviation mequ   :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<leftrightarrow>"48)
  where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longleftrightarrow>\<psi>(w)"  
abbreviation mexists   :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>") 
  where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. \<Phi>(x)(w)"
abbreviation mexistsB  :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<exists>"[8]9)
  where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"   
abbreviation meq    :: "\<mu>\<Rightarrow>\<mu>\<Rightarrow>\<sigma>" (infixr"\<^bold>="52) (*-- "Equality"  *)
  where "x\<^bold>=y \<equiv> \<lambda>w. x = y"
abbreviation mbox   :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<box>_"[52]53)
  where "\<^bold>\<box>\<phi> \<equiv> \<lambda>w.\<forall>v. w \<^bold>~ v \<longrightarrow> \<phi>(v)"
abbreviation mstit :: "\<mu> set \<Rightarrow> \<sigma>\<Rightarrow>\<sigma>" ("\<^bold>[_\<^bold>] _"[52]53)
  where "\<^bold>[G\<^bold>] \<phi> \<equiv> \<lambda>(w::i).\<forall>(v::i). (w ~ G  v) \<longrightarrow> \<phi>(v)"
abbreviation mstitDIA   :: "\<mu> set \<Rightarrow> \<sigma>\<Rightarrow>\<sigma>" ("\<^bold><_\<^bold>> _"[52]53)
  where "\<^bold><G\<^bold>> \<phi> \<equiv> \<lambda>(w::i).\<exists>(v::i). (w ~ G  v) \<and> \<phi>(v)"
abbreviation mdia   :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<diamond>_"[52]53)
  where "\<^bold>\<diamond>\<phi> \<equiv> \<lambda>w.\<exists>v. w \<^bold>~ v \<longrightarrow> \<phi>(v)"  

abbreviation valid :: "\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>"[8]109)
  where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p w"
abbreviation follows_w :: "i \<Rightarrow> \<sigma> \<Rightarrow> bool" (infix"\<^bold>\<Turnstile>"55)
  where "(w  \<^bold>\<Turnstile> p)  \<equiv> p w  "


abbreviation Deltamin  :: "\<mu> set \<Rightarrow> \<sigma>\<Rightarrow> i \<Rightarrow> bool" ("\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> _  _ "[52]53)
  where "((\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> (G::\<mu> set) (\<phi>::\<sigma>)) (\<tau>::i)) \<equiv>  ((\<^bold>[G\<^bold>] \<phi>) \<tau>) \<and> \<not>(\<exists> H. (H \<subset> G) \<and> ((\<^bold>[H\<^bold>] \<phi>) \<tau>))"

abbreviation deltamax  ::  "\<mu> set \<Rightarrow> \<sigma> \<Rightarrow> i \<Rightarrow> bool" ("\<^bold>\<Delta>\<^sup>m\<^sup>a\<^sup>x\<^sub> _ _")
  where "(\<^bold>\<Delta>\<^sup>m\<^sup>a\<^sup>x\<^sub> G \<phi>) \<tau>  \<equiv> G = {x. (\<exists>H. (((\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> H \<phi>) \<tau>) \<and> x \<in> H))}"

abbreviation BigIntersection :: "'a set set \<Rightarrow> 'a set" ("\<^bold>\<inter> _")
  where "\<^bold>\<inter> A \<equiv> {x. (\<exists>M \<in> A. (x \<in> M)) \<and> (\<forall> M \<in> A. x \<in> M)}" (*stupid hack*)

abbreviation Ness :: "\<mu> set \<Rightarrow> \<sigma> \<Rightarrow> i \<Rightarrow> bool" ("Ness\<^sub>_ _")
  where "(Ness\<^sub> G \<phi>) (\<tau>::i) \<equiv> (\<exists>(K::\<mu> set). (\<tau> \<^bold>\<Turnstile> (\<^bold>[K\<^bold>] \<phi>))) \<and> (\<forall>H. (\<tau> \<^bold>\<Turnstile> (\<^bold>[H\<^bold>] \<phi>))  \<longrightarrow>  \<not> (\<tau> \<^bold>\<Turnstile> (\<^bold>[H - G\<^bold>] \<phi>)))"

abbreviation Nessmin :: "\<mu> set \<Rightarrow> \<sigma> \<Rightarrow> i \<Rightarrow> bool" ("Ness\<^sup>m\<^sup>i\<^sup>n\<^sub>_ _")
  where "(Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>) (\<tau>::i) \<equiv> (Ness\<^sub> G \<phi> \<tau>) \<and> ( \<not>(\<exists> H. (H \<subset> G) \<and> (Ness\<^sub> H \<phi> \<tau>)))"

abbreviation Core :: "\<sigma> \<Rightarrow> i \<Rightarrow> \<mu> set" ("Core_ _")
  where "Core \<phi> \<tau>  \<equiv> \<^bold>\<inter> {H. (( \<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> H \<phi> )(\<tau>::i))}"

abbreviation nessmax :: "\<mu> set \<Rightarrow> \<sigma> \<Rightarrow> i \<Rightarrow> bool" ("Ness\<^sup>m\<^sup>a\<^sup>x\<^sub> _ _")
  where "(Ness\<^sup>m\<^sup>a\<^sup>x\<^sub> G \<phi>) \<tau>  \<equiv> G = {x. (\<exists>H. ((Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi> \<tau>) \<and> x \<in> H))}"

abbreviation sole :: "\<mu> set \<Rightarrow> \<sigma> \<Rightarrow> i \<Rightarrow> bool" ("\<^bold>\<Delta>\<^sup>s\<^sup>o\<^sup>l\<^sup>e\<^sub> _ _")
  where "(\<^bold>\<Delta>\<^sup>s\<^sup>o\<^sup>l\<^sup>e\<^sub> G \<phi>) \<equiv>(\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>)  \<^bold>\<and> (\<^bold>\<Delta>\<^sup>m\<^sup>a\<^sup>x\<^sub> G \<phi>)"

abbreviation Could :: "\<mu> set \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" ("Could\<^sub> _ _")
  where "Could\<^sub> G \<phi>  \<equiv> \<^bold><Ag - G\<^bold>> \<^bold>[Ag\<^bold>] \<phi>"
  
abbreviation Couldmin :: "\<mu> set \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" ("Could\<^sup>m\<^sup>i\<^sup>n\<^sub> _ _")
  where "(Could\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>) (\<tau>::i) \<equiv> ((Could\<^sub> G \<phi>) \<tau>) \<and>  \<not>(\<exists> H. (H \<subset> G) \<and> ((Could\<^sub> H \<phi>) \<tau>))"

abbreviation semanticOR :: "\<sigma> set \<Rightarrow> \<sigma>" ("\<^bold>\<Or> _")
  where "(\<^bold>\<Or> G ) (\<tau>::i) \<equiv> \<exists>\<phi> \<in> G. (\<phi> \<tau>)"

abbreviation alt :: "\<mu> \<Rightarrow> i \<Rightarrow> i set" ("alt\<^sub> _( _ )")
  where "alt\<^sub> x( \<tau> ) \<equiv> {\<tau>b. (~ x) \<tau> \<tau>b}"

abbreviation actiontypes :: "\<mu> \<Rightarrow> i set set" ("\<^bold>A\<^sub> _")
  where "\<^bold>A\<^sub> x \<equiv> {v. \<exists>\<tau>. v = alt\<^sub> x (\<tau>)}"

end