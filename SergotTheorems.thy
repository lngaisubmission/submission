theory SergotTheorems

imports Main Sergot

begin

lemma Superadditivity: "G \<subseteq> H \<longrightarrow> \<lfloor>(\<^bold>[G\<^bold>]\<phi>) \<^bold>\<rightarrow> (\<^bold>[H\<^bold>]\<phi>)\<rfloor>" by auto
(*To add: s5 stuff*)

lemma IntEmptyBox: "(\<not> (\<exists>x. (x \<in> G \<inter> H))) \<longrightarrow> \<lfloor>(\<^bold>[G\<^bold>]\<^bold>[H\<^bold>]\<phi>) \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<rfloor>"
  oops (*nitpick finds counterexample*)

lemma helper1: "\<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub>H \<phi>) \<longrightarrow> H \<subseteq> G \<longrightarrow> \<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub>H \<phi>)" by blast

lemma helper2: "(\<tau> \<^bold>\<Turnstile> (\<^bold>[G\<^bold>]\<phi>)) \<longrightarrow> (\<exists>H\<subseteq>G. (\<not> (\<exists>K\<subset>H. (\<^bold>[K\<^bold>]\<phi>) \<tau>)))" by blast


lemma NessCompHelper: "(Ness\<^sup>m\<^sup>a\<^sup>x\<^sub>G \<phi>) \<tau> \<longrightarrow> x \<in> G \<longrightarrow> (\<exists>H. (Ness\<^sup>m\<^sup>i\<^sup>n\<^sub>H \<phi> \<tau>) \<and> x \<in> H)"
proof - 
  {fix "G" "\<phi>" "\<tau>" "x"
    {assume 1: "(Ness\<^sup>m\<^sup>a\<^sup>x\<^sub> G \<phi>) \<tau>" and 2: "x \<in> G"
      hence "G = {x. (\<exists>H. ((Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi> \<tau>) \<and> x \<in> H))}" by simp
      hence "(\<exists>H. ((Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi> \<tau>) \<and> x \<in> H))" using 2 by blast}
    hence "(Ness\<^sup>m\<^sup>a\<^sup>x\<^sub> G \<phi>) \<tau> \<longrightarrow> x \<in> G \<longrightarrow> (\<exists>H. (Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> H \<phi> \<tau>) \<and> x \<in> H)" by blast}
  thus ?thesis by auto
qed

lemma Nesses: "(Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>) = (Ness\<^sub> G \<phi>) \<^bold>\<and> (\<^bold>\<not> \<^bold>\<Or> {x.\<exists>H. H \<subset> G \<and> x = (Ness\<^sub> H \<phi>)})"
proof - 
  {fix "G" "\<phi>"
  {fix "\<tau>"
  {assume "\<tau> \<^bold>\<Turnstile> (Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>)"
    hence "\<tau> \<^bold>\<Turnstile> ((Ness\<^sub> G \<phi>) \<^bold>\<and> (\<^bold>\<not> \<^bold>\<Or> {x.\<exists>H.  H \<subset> G \<and> x = (Ness\<^sub> H \<phi>)}))" using mem_Collect_eq by blast}
  hence l: "\<tau> \<^bold>\<Turnstile> (Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>) \<longrightarrow> \<tau> \<^bold>\<Turnstile> ((Ness\<^sub> G \<phi>) \<^bold>\<and> (\<^bold>\<not> \<^bold>\<Or> {x.\<exists>H.  H \<subset> G \<and> x = (Ness\<^sub> H \<phi>)}))" by blast
  {assume asm2: "\<tau> \<^bold>\<Turnstile> ((Ness\<^sub> G \<phi>) \<^bold>\<and> (\<^bold>\<not> \<^bold>\<Or> {x.\<exists>H.  H \<subset> G \<and> x = (Ness\<^sub> H \<phi>)}))"
    {assume "((\<exists> H. (H \<subset> G) \<and> (Ness\<^sub> H \<phi> \<tau>)))"
    then obtain K where " (K \<subset> G) \<and> (Ness\<^sub> K \<phi> \<tau>)" by auto
    hence "\<tau> \<^bold>\<Turnstile> \<^bold>\<Or> {x.\<exists>H.  H \<subset> G \<and> x = (Ness\<^sub> H \<phi>)}" by auto
    hence False using asm2 by simp}
  hence "\<tau> \<^bold>\<Turnstile> (Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>)" using asm2 by argo}
  hence "\<tau> \<^bold>\<Turnstile> ((Ness\<^sub> G \<phi>) \<^bold>\<and> (\<^bold>\<not> \<^bold>\<Or> {x.\<exists>H.  H \<subset> G \<and> x = (Ness\<^sub> H \<phi>)})) \<longrightarrow> \<tau> \<^bold>\<Turnstile> (Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>)" by blast
  hence "\<tau> \<^bold>\<Turnstile> (Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>) \<longleftrightarrow> \<tau> \<^bold>\<Turnstile> ((Ness\<^sub> G \<phi>) \<^bold>\<and> (\<^bold>\<not> \<^bold>\<Or> {x.\<exists>H. H \<subset> G \<and> x = (Ness\<^sub> H \<phi>)}))" using l by argo}
  hence "(Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>) = (Ness\<^sub> G \<phi>) \<^bold>\<and> (\<^bold>\<not> \<^bold>\<Or> {x.\<exists>H. H \<subset> G \<and> x = (Ness\<^sub> H \<phi>)})" by simp}
  thus ?thesis by simp
qed

abbreviation dumbFunction :: "\<mu> set \<Rightarrow> (\<mu> set \<Rightarrow> bool) \<Rightarrow> nat"
  where "dumbFunction G Rel \<equiv> Min {n. \<exists>H. H \<subseteq> G \<and> n = card H \<and> Rel H}"

lemma RelFinite: "(Rel::\<mu> set \<Rightarrow> bool) G \<longrightarrow> finite {n. \<exists>H. H \<subseteq> G \<and> n = card H \<and> Rel H}"
proof -
{fix Rel G
    {assume "(Rel::\<mu> set \<Rightarrow> bool) G"
      let ?m = "card Ag"
      have "\<forall>a. a \<in> {n. \<exists>H. H \<subseteq> G \<and> n = card H \<and> Rel H} \<longrightarrow> a \<le> ?m" using card_mono finiteActors by blast
      hence a: "finite {n. \<exists>H. H \<subseteq> G \<and> n = card H \<and> Rel H}" by (meson finite_nat_set_iff_bounded_le)}
    hence "(Rel::\<mu> set \<Rightarrow> bool) G \<longrightarrow> finite  {n. \<exists>H. H \<subseteq> G \<and> n = card H \<and> Rel H}" by blast}
  thus ?thesis by simp
qed


lemma "Rel G \<longrightarrow> dumbFunction G Rel \<le> card G"
proof -
  {fix Rel G
    {assume "(Rel::\<mu> set \<Rightarrow> bool) G"
      let ?m = "card Ag"
      have a: "finite {n. \<exists>H. H \<subseteq> G \<and> n = card H \<and> Rel H}" using RelFinite \<open>Rel G\<close> by presburger
      have "G \<subseteq> G \<and> card G = card G \<and> Rel G" using \<open>Rel G\<close> by blast
      hence "card G \<in> {n. \<exists>H. H \<subseteq> G \<and> n = card H \<and> Rel H}" by auto
      hence "{} \<noteq> {n. \<exists>H. H \<subseteq> G \<and> n = card H \<and> Rel H}" by blast
      hence "dumbFunction G Rel \<le> ?m" using a by (metis (no_types, lifting) Min_le_iff \<open>card G \<in> {n. \<exists>H\<subseteq>G. n = card H \<and> Rel H}\<close> card_mono finiteActors top_greatest)
      hence "card G \<ge> dumbFunction G Rel" using Min_le \<open>Rel G\<close> a by blast}
    hence "Rel G \<longrightarrow> dumbFunction G Rel \<le> card G" by simp}
  thus ?thesis by simp
qed

lemma minimalexists: "(Rel::\<mu> set \<Rightarrow> bool) G \<longrightarrow> (\<exists>H\<subseteq>G. Rel H \<and> (\<not> (\<exists>K \<subset> H. (Rel K))))" 
proof - 
  {fix Rel G
    {assume "(Rel::\<mu> set \<Rightarrow> bool) G"
      hence "\<exists>n. (n = dumbFunction G Rel)" by simp
      then obtain n where obtn: "n = dumbFunction G Rel" by auto
      have "finite {n. \<exists>H. H \<subseteq> G \<and> n = card H \<and> Rel H}" using RelFinite \<open>Rel G\<close> by presburger
      hence "\<exists>H. H \<subseteq> G \<and> n = card H \<and> Rel H" using Min_in obtn \<open>Rel G\<close> by auto
      then obtain H where obtH: "H \<subseteq> G \<and> n = card H \<and> Rel H" by auto
      {assume red: "\<exists>K \<subset> H. (Rel K)"
        then obtain K where obtK: "K \<subset> H \<and> (Rel K)" by auto
        hence "K \<subseteq> G \<and> Rel K" using obtH by blast
        hence c: "card K \<in> {n. \<exists>H. H \<subseteq> G \<and> n = card H \<and> Rel H}" by auto
        have "card K < n" using obtK by (metis finiteActors finite_subset obtH psubset_card_mono top_greatest)
        hence False using Min_le \<open>finite {n. \<exists>H\<subseteq>G. n = card H \<and> Rel H}\<close> c not_less obtn by blast}
      hence "\<not> (\<exists>K \<subset> H. (Rel K))" by blast
      hence "(\<exists>H\<subseteq>G. Rel H \<and> (\<not> (\<exists>K \<subset> H. (Rel K))))" using obtH by auto}
    hence "(Rel::\<mu> set \<Rightarrow> bool) G \<longrightarrow> (\<exists>H\<subseteq>G. Rel H \<and> (\<not> (\<exists>K \<subset> H. (Rel K))))" by simp}
  thus ?thesis by simp
qed

lemma Proposition1: "(\<tau> \<^bold>\<Turnstile> (Ness\<^sub> G \<phi>) \<longleftrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>[Ag\<^bold>]\<phi>)) \<and> \<not>(\<tau> \<^bold>\<Turnstile> (\<^bold>[Ag - G\<^bold>]\<phi>)))" by blast

lemma "(G \<subseteq> H) \<longrightarrow> \<lfloor>(\<^bold>\<not>(\<^bold>[Ag -H\<^bold>]\<phi>)) \<^bold>\<rightarrow> (\<^bold>\<not>(\<^bold>[Ag-H\<^bold>]\<phi>))\<rfloor>" by auto

lemma Proposition2a: "(Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x} \<phi> \<tau>) \<longrightarrow> x \<in> (Core \<phi> \<tau>)"
proof- 
  {fix x \<phi> \<tau>
    assume asm: "(Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x::\<mu>} \<phi> (\<tau>::i))"
      {assume red: "x \<notin> (Core \<phi> \<tau>)"
        from asm have "(Ness\<^sub> {x} \<phi> \<tau>) \<and> ((\<forall>H \<subset> {x}. \<not> (Ness\<^sub> H \<phi> \<tau>)))" by blast
        hence "(Ness\<^sub> {x} \<phi> \<tau>) \<and> \<not> (Ness\<^sub> {} \<phi> \<tau>)" by blast
        hence a: "(Ness\<^sub> {x} \<phi> \<tau>)" by simp
        from Proposition1 have p1: "(\<tau> \<^bold>\<Turnstile> (Ness\<^sub> {x} \<phi>) \<longleftrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>[Ag\<^bold>]\<phi>)) \<and> \<not>(\<tau> \<^bold>\<Turnstile> (\<^bold>[Ag - {x}\<^bold>]\<phi>)))" by presburger
        hence "\<not> (\<^bold>[Ag -{x}\<^bold>]\<phi>) \<tau>" using a by simp
        have ag: "(\<^bold>[Ag\<^bold>]\<phi>) \<tau>" using p1 a by simp
        let ?Rel = "\<lambda>K. (\<^bold>[K\<^bold>]\<phi>) \<tau>"
        from minimalexists have "\<forall> Rel G.(Rel::\<mu> set \<Rightarrow> bool) G \<longrightarrow> (\<exists>H\<subseteq>G. Rel H \<and> (\<not> (\<exists>K \<subset> H. (Rel K))))" by simp
        hence "\<forall> Rel.(Rel::\<mu> set \<Rightarrow> bool) Ag \<longrightarrow> (\<exists>H\<subseteq>Ag. Rel H \<and> (\<not> (\<exists>K \<subset> H. (Rel K))))" by blast
        hence "(?Rel::\<mu> set \<Rightarrow> bool) Ag \<longrightarrow> (\<exists>H\<subseteq>Ag. ?Rel H \<and> (\<not> (\<exists>K \<subset> H. (?Rel K))))" by (rule allE)
        hence "(\<exists>H\<subseteq>Ag. ?Rel H \<and> (\<not> (\<exists>K \<subset> H. (?Rel K))))" using ag by simp
        then obtain H where obtH: "H \<subseteq> Ag \<and> ((\<^bold>[H\<^bold>]\<phi>) \<tau>) \<and> (\<not> (\<exists>K \<subset> H. ((\<^bold>[K\<^bold>]\<phi>) \<tau>)))" by auto
        hence ex: "\<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> H \<phi>)" by simp
        hence ex2: "x \<in> H" by (metis DiffI UNIV_I \<open>\<not> \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> (Ag - {x}) \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor>\<close> singletonD)
        from red have "x \<notin> \<^bold>\<inter> {H. ((\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> H \<phi>)(\<tau>::i))}" by simp
        hence  "x \<notin> {x. (\<exists>M \<in> {H. ((\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> H \<phi>)(\<tau>::i))}. (x \<in> M)) \<and> (\<forall> M \<in> {H. ((\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> H \<phi>)(\<tau>::i))}. x \<in> M)}" by simp
        hence "\<exists>K. (\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> K \<phi>)(\<tau>::i) \<and> x \<notin> K" using ex ex2 by blast
        then obtain K where obtK: "(\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> K \<phi>)(\<tau>::i) \<and> x \<notin> K" by auto
          hence "(\<^bold>[Ag -{x}\<^bold>]\<phi>) \<tau>" by auto
          hence False using \<open>((\<exists>K. \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> K \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor>) \<and> (\<forall>H. \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> H \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor> \<longrightarrow> \<not> \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> (H - {x}) \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor>)) \<and> (\<forall>H\<subset>{x}. \<not> ((\<exists>K. \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> K \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor>) \<and> (\<forall>Ha. \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> Ha \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor> \<longrightarrow> \<not> \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> (Ha - H) \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor>)))\<close> p1 by blast}
        hence "x \<in> Core \<phi> \<tau>" by blast}
      thus ?thesis by presburger
qed

lemma Proposition2b: "(x \<in> (Core \<phi> \<tau>)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x} \<phi>))"
proof -
    {assume "x \<in> (Core \<phi> \<tau>)"
      {assume "\<not> (\<tau> \<^bold>\<Turnstile> (Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x} \<phi>))"
        hence a: "(\<not> Ness\<^sub> {x} \<phi> \<tau>) \<or> ((\<exists> H. (H \<subset> {x}) \<and> (Ness\<^sub> H \<phi> \<tau>)))" by blast
        have "(\<exists> H. (H \<subset> {x}) \<and> (Ness\<^sub> H \<phi> \<tau>)) \<longleftrightarrow> (Ness\<^sub> {} \<phi> \<tau>)" by fast
        hence "(\<not> (Ness\<^sub> {x} \<phi> \<tau>)) \<or> (Ness\<^sub> {} \<phi> \<tau>)" using a by auto
        {assume "(Ness\<^sub> {} \<phi> \<tau>)"
          hence False by auto}
        {assume "(\<not> (Ness\<^sub> {x} \<phi> \<tau>))"
          hence "(\<not> (\<exists>(K::\<mu> set). (\<tau> \<^bold>\<Turnstile> (\<^bold>[K\<^bold>]\<phi>)))) \<or> (\<exists>H. (\<tau> \<^bold>\<Turnstile> (\<^bold>[H\<^bold>]\<phi>)) \<and> (\<tau> \<^bold>\<Turnstile> (\<^bold>[H - {x}\<^bold>]\<phi>)))" by blast
          {assume "\<not> (\<exists>(K::\<mu> set). (\<tau> \<^bold>\<Turnstile> (\<^bold>[K\<^bold>]\<phi>)))"
            hence False using \<open>x \<in> \<^bold>\<inter> {H. \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> H \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor> \<and> \<not> (\<exists>Ha\<subset>H. \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> Ha \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor>)}\<close> by auto}
          {assume "\<exists>H. (\<tau> \<^bold>\<Turnstile> (\<^bold>[H\<^bold>]\<phi>)) \<and> (\<tau> \<^bold>\<Turnstile> (\<^bold>[H - {x}\<^bold>]\<phi>))"
            then obtain H where obtH: "(\<tau> \<^bold>\<Turnstile> (\<^bold>[H\<^bold>]\<phi>)) \<and> (\<tau> \<^bold>\<Turnstile> (\<^bold>[H - {x}\<^bold>]\<phi>))" by auto
            let ?Rel = "\<lambda>K. (\<^bold>[K\<^bold>]\<phi>) \<tau>" 
            from minimalexists have "\<forall> Rel G.(Rel::\<mu> set \<Rightarrow> bool) G \<longrightarrow> (\<exists>L\<subseteq>G. Rel L \<and> (\<not> (\<exists>K \<subset> L. (Rel K))))" by simp
            hence "\<forall> Rel.(Rel::\<mu> set \<Rightarrow> bool) (H - {x}) \<longrightarrow> (\<exists>L\<subseteq>(H - {x}). Rel L \<and> (\<not> (\<exists>K \<subset> L. (Rel K))))" by simp
            hence "(?Rel::\<mu> set \<Rightarrow> bool) (H - {x}) \<longrightarrow> (\<exists>L\<subseteq>(H - {x}). ?Rel L \<and> (\<not> (\<exists>K \<subset> L. (?Rel K))))" by (rule allE)
            hence " (\<exists>L\<subseteq>(H - {x}). ?Rel L \<and> (\<not> (\<exists>K \<subset> L. (?Rel K))))" using obtH by fastforce
            hence "\<exists>K. (\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> K \<phi>)(\<tau>::i) \<and> x \<notin> K" by (metis subset_Diff_insert)
            hence "x \<notin> Core \<phi> \<tau>" by simp
            hence False using \<open>x \<in> \<^bold>\<inter> {H. \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> H \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor> \<and> \<not> (\<exists>Ha\<subset>H. \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> Ha \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor>)}\<close> by blast}
          hence False using \<open>\<nexists>K. \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> K \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor> \<Longrightarrow> False\<close> \<open>\<not> ((\<exists>K. \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> K \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor>) \<and> (\<forall>H. \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> H \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor> \<longrightarrow> \<not> \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> (H - {x}) \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor>))\<close> by blast}
        hence False using \<open>(\<exists>K. \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> K \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor>) \<and> (\<forall>H. \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> H \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor> \<longrightarrow> \<not> \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> (H - {}) \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor>) \<Longrightarrow> False\<close> \<open>\<not> ((\<exists>K. \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> K \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor>) \<and> (\<forall>H. \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> H \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor> \<longrightarrow> \<not> \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> (H - {x}) \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor>)) \<or> (\<exists>K. \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> K \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor>) \<and> (\<forall>H. \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> H \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor> \<longrightarrow> \<not> \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> (H - {}) \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor>)\<close> by fastforce}
      hence "(\<tau> \<^bold>\<Turnstile> (Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x::\<mu>} \<phi>))" by blast}
    thus "(x \<in> (Core \<phi> \<tau>)) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x::\<mu>} \<phi>))" by blast
  qed

lemma Proposition2: "(Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x} \<phi> \<tau>) \<longleftrightarrow> x \<in> (Core \<phi> \<tau>)"
proof - 
  {assume "\<not> ((Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x::\<mu>} \<phi> (\<tau>::i)) \<longleftrightarrow> x \<in> (Core \<phi> \<tau>))"
    hence or: " (\<not> ((Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x::\<mu>} \<phi> (\<tau>::i)) \<longrightarrow> x \<in> (Core \<phi> \<tau>))) \<or> \<not> ((x \<in> (Core \<phi> \<tau>)) \<longrightarrow> (Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x::\<mu>} \<phi> (\<tau>::i)))" by blast
    from Proposition2b have "((x \<in> (Core \<phi> \<tau>)) \<longrightarrow> (Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x} \<phi> \<tau>))" by -
    hence or2: "(\<not> ((Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x::\<mu>} \<phi> (\<tau>::i)) \<longrightarrow> x \<in> (Core \<phi> \<tau>)))" using or by blast
    from Proposition2a have "((Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x::\<mu>} \<phi> (\<tau>::i)) \<longrightarrow> x \<in> (Core \<phi> \<tau>))" by -
    hence False using or2 by blast}
  thus ?thesis by argo
qed


lemma minDeltaExists: "(\<tau> \<^bold>\<Turnstile> (\<^bold>[G\<^bold>]\<phi>)) \<longrightarrow> (\<exists>H \<subseteq> G. (\<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> H \<phi>)))"
proof - 
  let ?Rel = "\<lambda>K. (\<^bold>[K\<^bold>]\<phi>) \<tau>"
  from minimalexists have"\<forall>Rel. (Rel::\<mu> set \<Rightarrow> bool) G \<longrightarrow> (\<exists>H\<subseteq>G. Rel H \<and> (\<not> (\<exists>K \<subset> H. (Rel K))))" by simp
  hence "(?Rel::\<mu> set \<Rightarrow> bool) G \<longrightarrow> (\<exists>H\<subseteq>G. ?Rel H \<and> (\<not> (\<exists>K \<subset> H. (?Rel K))))" by (rule allE)
  thus "(\<tau> \<^bold>\<Turnstile> (\<^bold>[G\<^bold>]\<phi>)) \<longrightarrow> (\<exists>H\<subseteq>G. (\<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> H \<phi>)))" by auto
qed

lemma Corollary1a: "(G \<noteq> {}) \<longrightarrow> (((\<tau> \<^bold>\<Turnstile> (\<^bold>[G\<^bold>]\<phi>)) \<and> (G = Core \<phi> \<tau>)) \<longrightarrow> \<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>s\<^sup>o\<^sup>l\<^sup>e\<^sub> G \<phi>))"
proof - 
  {assume asm1: "G \<noteq> {}"
    and asm2: "\<tau> \<^bold>\<Turnstile> (\<^bold>[G\<^bold>]\<phi>)" 
    and asm3: "G = Core \<phi> \<tau>"
    {assume red:"(\<exists> H. (H \<subset> G) \<and> ((\<^bold>[H\<^bold>]\<phi>) \<tau>))"
      then obtain H where obtH: "(H \<subset> G) \<and> ((\<^bold>[H\<^bold>]\<phi>) \<tau>)" by auto
      {assume "H = {}"
        hence "Core \<phi> \<tau> = {}" using obtH by auto
        hence False using asm3 obtH asm1 by fastforce}
      hence ne: "H \<noteq> {}" by blast
      hence "\<exists>x\<in>G. x \<notin> H" using obtH by blast
      then obtain x where obtx: "x \<in> G \<and> x \<notin> H" by auto
      have "Core \<phi> \<tau> \<noteq> {}" using asm1 asm3 by simp
      hence fa: "\<forall>y. ((y \<in> Core \<phi> \<tau>) \<longrightarrow> (\<forall>K. (\<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> K \<phi>)) \<longrightarrow> y \<in> K))" by simp
      from minDeltaExists obtH have "\<exists>K\<subseteq>H. (\<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> K \<phi>))" by simp
      then obtain K where obtK: "K\<subseteq>H \<and> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> K \<phi>))" by auto
      hence "x \<notin> K" using obtx by auto
      hence "\<exists>K. (\<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> K \<phi>)) \<and> x \<notin> K" using obtK by auto
      hence "x \<notin> Core \<phi> \<tau>" using fa by force
      hence False using obtx asm3 by blast}
    hence "\<not> (\<exists> H. (H \<subset> G) \<and> ((\<^bold>[H\<^bold>]\<phi>) \<tau>))" by blast
    hence one: "\<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>)" using asm2 by simp
    {assume red2: "\<not> (\<^bold>\<Delta>\<^sup>m\<^sup>a\<^sup>x\<^sub> G \<phi>) \<tau>" 
      from one have "\<exists>M. (\<^bold>\<Delta>\<^sup>m\<^sup>a\<^sup>x\<^sub> M \<phi>) \<tau>" by presburger
      then obtain M where obtmax: "(\<^bold>\<Delta>\<^sup>m\<^sup>a\<^sup>x\<^sub> M \<phi>) \<tau>" by auto
      {assume "G \<noteq> M"
        hence a: "M \<supset> G " using obtmax Collect_mono_iff asm3 mem_Collect_eq psubsetI by auto
        hence "\<exists>x\<in>M. x\<notin>G" by auto
        then obtain x where obtx: "x \<in> M \<and> x \<notin> G" by auto
        hence "x \<in> {x. (\<exists>K. (((\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> K \<phi>) \<tau>) \<and> x \<in> K))}" using obtmax by simp
        hence "\<exists>H. ((\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> H \<phi>) \<tau>) \<and> x \<in> H" by simp
        then obtain H where obtH: "(\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> H \<phi>) \<tau> \<and> x \<in> H" by auto
        {assume "\<exists>y \<in> G. y \<notin> H"
          then obtain y where obty: "y \<in> G \<and> y \<notin> H" by auto
          hence "y \<notin> Core \<phi> \<tau>" using obtH by auto
          hence False using asm3 obty by argo}
        hence "H \<supseteq> G" by auto
        hence "H \<supset> G" using obtx obtH by auto
        hence False using obtH asm2 by blast}
      hence "G = M" by blast
      hence "(\<^bold>\<Delta>\<^sup>m\<^sup>a\<^sup>x\<^sub> G \<phi>) \<tau>" using obtmax by auto
      hence False using red2 by blast}
    hence "(\<^bold>\<Delta>\<^sup>m\<^sup>a\<^sup>x\<^sub> G \<phi>) \<tau>" by blast
    hence "\<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>s\<^sup>o\<^sup>l\<^sup>e\<^sub> G \<phi>)" using one by blast}
  thus ?thesis by argo
qed

lemma Corollary1b: "(G \<noteq> {}) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>s\<^sup>o\<^sup>l\<^sup>e\<^sub> G \<phi>) \<longrightarrow> ((\<tau> \<^bold>\<Turnstile> (\<^bold>[G\<^bold>]\<phi>)) \<and> (G = Core \<phi> \<tau>)))"
proof -
    {assume asm: "G \<noteq> {}" and asm2: "\<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>s\<^sup>o\<^sup>l\<^sup>e\<^sub> G \<phi>)"
      hence 1: "\<tau> \<^bold>\<Turnstile> (\<^bold>[G\<^bold>]\<phi>)" by blast
      have 2: "\<not>(\<exists> H. (H \<subset> G) \<and> (\<^bold>[H\<^bold>]\<phi>) \<tau>)" using asm2 by argo
      have "Core \<phi> \<tau> \<subseteq> G" using asm2 by blast
      have "G \<subseteq> Core \<phi> \<tau>" 
      proof -
      {assume red: "\<exists>x. x \<in> G \<and> x \<notin> Core \<phi> \<tau>"
        then obtain x where obtx: "x \<in> G \<and> x \<notin> Core \<phi> \<tau>" by presburger
        hence nm: "\<not> (Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x} \<phi> \<tau>)" using Proposition2 by simp
        have "\<not> \<tau> \<^bold>\<Turnstile> (\<^bold>[{}\<^bold>]\<phi>)" using 1 2 asm by blast
        hence "\<not>(\<exists> H. (H \<subset> {x}) \<and> (Ness\<^sub> H \<phi> \<tau>))" by (metis Diff_empty Diff_insert_absorb bot.extremum_strict less_imp_le psubset_insert_iff singleton_insert_inj_eq)
        hence nn: "\<not> Ness\<^sub> {x} \<phi> \<tau>" using nm by blast
        from 1 have "\<tau> \<^bold>\<Turnstile> (\<^bold>[Ag\<^bold>]\<phi>)" by simp
        hence "\<tau> \<^bold>\<Turnstile> (\<^bold>[Ag - {x}\<^bold>]\<phi>)" using Proposition1 nn by blast 
        have ff: "\<forall>H. \<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> H \<phi>) \<longrightarrow> x \<in> H"
        proof -
          {fix H
            assume asmH: "\<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> H \<phi>)"
              hence "H \<subseteq> G" using asm2 by blast
              hence "H = G" using asmH \<open>H \<subseteq> G\<close> using asm2 by (meson order.not_eq_order_implies_strict)
              hence "x \<in> H" by (simp add: obtx)}
            thus "\<forall>H. \<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> H \<phi>) \<longrightarrow> x \<in> H" by simp
          qed
          have "\<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> (G::\<mu> set) \<phi>)" using 1 2 by simp
          hence "x \<in> Core \<phi> \<tau>" using ff by auto
          hence False using obtx by fastforce}
        thus ?thesis by blast
      qed
      hence "G = Core \<phi> \<tau>" using \<open>\<^bold>\<inter> {H. \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> H \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor> \<and> \<not> (\<exists>Ha\<subset>H. \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> Ha \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor>)} \<subseteq> G\<close> by blast}
    thus "(G \<noteq> {}) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>s\<^sup>o\<^sup>l\<^sup>e\<^sub> G \<phi>) \<longrightarrow> ((\<tau> \<^bold>\<Turnstile> (\<^bold>[G\<^bold>]\<phi>)) \<and> (G = Core \<phi> \<tau>)))" by argo
qed

lemma Corollary1: "G \<noteq> {} \<longrightarrow>(((\<tau> \<^bold>\<Turnstile> (\<^bold>[G\<^bold>]\<phi>)) \<and> (G = Core \<phi> \<tau>)) \<longleftrightarrow> \<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>s\<^sup>o\<^sup>l\<^sup>e\<^sub> G \<phi>))"
proof -
  {assume asm: "G \<noteq> {}"
    have "G \<noteq> {} \<longrightarrow> (((\<tau> \<^bold>\<Turnstile> (\<^bold>[G\<^bold>]\<phi>)) \<and> (G = Core \<phi> \<tau>)) \<longrightarrow> \<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>s\<^sup>o\<^sup>l\<^sup>e\<^sub> G \<phi>))" using Corollary1a by -
    hence lr: "(((\<tau> \<^bold>\<Turnstile> (\<^bold>[G\<^bold>]\<phi>)) \<and> (G = Core \<phi> \<tau>)) \<longrightarrow> \<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>s\<^sup>o\<^sup>l\<^sup>e\<^sub> G \<phi>))" using asm by (rule mp)
    have "(G \<noteq> {}) \<longrightarrow> (\<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>s\<^sup>o\<^sup>l\<^sup>e\<^sub> G \<phi>) \<longrightarrow> ((\<tau> \<^bold>\<Turnstile> (\<^bold>[G\<^bold>]\<phi>)) \<and> (G = Core \<phi> \<tau>)))" using Corollary1b by -
    hence "(\<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>s\<^sup>o\<^sup>l\<^sup>e\<^sub> G \<phi>) \<longrightarrow> ((\<tau> \<^bold>\<Turnstile> (\<^bold>[G\<^bold>]\<phi>)) \<and> (G = Core \<phi> \<tau>)))" using asm by (rule mp)
    hence "(((\<tau> \<^bold>\<Turnstile> (\<^bold>[G\<^bold>]\<phi>)) \<and> (G = Core \<phi> \<tau>)) \<longleftrightarrow> \<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>s\<^sup>o\<^sup>l\<^sup>e\<^sub> G \<phi>))" using lr by argo}
  thus ?thesis by blast (*this whole proof is pointless, but my hardware cant prove it on its own*)
qed

lemma Proposition3: "G \<noteq> {} \<longrightarrow>((\<tau> \<^bold>\<Turnstile> (Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>)) \<longleftrightarrow> (G \<subseteq> H) \<and> (\<tau> \<^bold>\<Turnstile>((\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub>H \<phi>) \<^bold>\<and> \<^bold>\<not>\<^bold>[H - G\<^bold>]\<phi>)) \<and> (\<not> (\<exists>K. K \<subset> H \<and> (\<tau> \<^bold>\<Turnstile>((\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub>K \<phi>) \<^bold>\<and> \<^bold>\<not>\<^bold>[K - G\<^bold>]\<phi>)))))" 
  oops
(*Nitpick finds a counterexample here too*)

lemma Proposition3a: "G \<noteq> {} \<longrightarrow>((\<tau> \<^bold>\<Turnstile> (Ness\<^sup>m\<^sup>i\<^sup>n\<^sub>G \<phi>)) \<longrightarrow> (G \<subseteq> H) \<and> (\<tau> \<^bold>\<Turnstile>((\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub>H \<phi>) \<^bold>\<and> \<^bold>\<not>\<^bold>[H - G\<^bold>]\<phi>)) \<and> (\<not> (\<exists>K. K \<subset> H \<and> (\<tau> \<^bold>\<Turnstile>((\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub>K \<phi>) \<^bold>\<and> \<^bold>\<not>\<^bold>[K - G\<^bold>]\<phi>)))))" nitpick[user_axioms]
  oops
(*Nitpick finds a counterexample here too*)
lemma Proposition3b: "G \<noteq> {} \<longrightarrow> ((G \<subseteq> H) \<and> (\<tau> \<^bold>\<Turnstile>((\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub>H \<phi>) \<^bold>\<and> \<^bold>\<not>\<^bold>[H - G\<^bold>]\<phi>)) \<and> (\<not> (\<exists>K. K \<subset> H \<and> (\<tau> \<^bold>\<Turnstile>((\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> K \<phi>) \<^bold>\<and> \<^bold>\<not>\<^bold>[K - G\<^bold>]\<phi>)))) \<longrightarrow> ((\<tau> \<^bold>\<Turnstile> (Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>))))" nitpick[user_axioms]
  oops
(*Nitpick finds a counterexample here too*)


lemma Proposition5: "G \<noteq> {} \<longrightarrow> \<lfloor>(\<^bold>[Ag\<^bold>]\<phi>) \<^bold>\<rightarrow> ((Could\<^sub> G (\<^bold>\<not>\<phi>)) \<^bold>\<rightarrow> (Ness\<^sub> G \<phi>))\<rfloor>" by (meson DiffD2 DiffI iso_tuple_UNIV_I tildexeq xsub)

lemma eqcompr: "(\<forall>\<tau>. \<tau> \<^bold>\<Turnstile> \<phi> \<longleftrightarrow> \<tau> \<^bold>\<Turnstile> \<psi>) \<longleftrightarrow> \<phi> = \<psi>"
proof- 
  have rl: "\<phi> = \<psi> \<longrightarrow> (\<forall>\<tau>. \<tau> \<^bold>\<Turnstile> \<phi> \<longleftrightarrow> \<tau> \<^bold>\<Turnstile> \<psi>)" by simp
  have "(\<forall>\<tau>. \<tau> \<^bold>\<Turnstile> \<phi> \<longleftrightarrow> \<tau> \<^bold>\<Turnstile> \<psi>) \<longrightarrow> \<phi> = \<psi>" by auto
  thus ?thesis using rl by blast
qed

lemma NessEq: "Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x} \<phi> = Ness\<^sub> {x} \<phi>"
proof -
  {fix \<tau>
    {assume "\<tau> \<^bold>\<Turnstile> Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x} \<phi>"
      hence "\<tau> \<^bold>\<Turnstile>Ness\<^sub> {x} \<phi>" by simp}
    {assume "\<tau> \<^bold>\<Turnstile>Ness\<^sub> {x} \<phi>" 
      hence "\<not> \<tau> \<^bold>\<Turnstile>(\<^bold>[{}\<^bold>]\<phi>)" by (meson equals0D)
      hence " \<not>(\<exists> H. (H \<subset> {x}) \<and> (Ness\<^sub> H \<phi> \<tau>))" by (metis Diff_empty Diff_insert_absorb bot.extremum_strict less_imp_le psubset_insert_iff singleton_insert_inj_eq)
      hence "\<tau> \<^bold>\<Turnstile> Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x} \<phi>" using \<open>(\<exists>K. \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> K \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor>) \<and> (\<forall>H. \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> H \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor> \<longrightarrow> \<not> \<lfloor>(\<lambda>v. v \<^bold>\<Turnstile> tildeG \<tau> (H - {x}) \<longrightarrow> v \<^bold>\<Turnstile> \<phi>)\<rfloor>)\<close> by blast}
    hence "\<tau> \<^bold>\<Turnstile> Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x} \<phi> \<longleftrightarrow> \<tau> \<^bold>\<Turnstile> Ness\<^sub> {x} \<phi>" by blast}
  hence a: "\<forall>\<tau>. (\<tau> \<^bold>\<Turnstile> Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x} \<phi> \<longleftrightarrow> \<tau> \<^bold>\<Turnstile> Ness\<^sub> {x} \<phi>)" by simp
  from eqcompr have "\<forall>z y. ((\<forall>\<tau>. \<tau> \<^bold>\<Turnstile> z \<longleftrightarrow> \<tau> \<^bold>\<Turnstile> y) \<longleftrightarrow> z = y)" by simp
  hence "\<forall>y. ((\<forall>\<tau>. \<tau> \<^bold>\<Turnstile> (Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x} \<phi>) \<longleftrightarrow> \<tau> \<^bold>\<Turnstile> y) \<longleftrightarrow> (Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x} \<phi>) = y)" by (rule allE)
  hence "((\<forall>\<tau>. \<tau> \<^bold>\<Turnstile> (Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x} \<phi>) \<longleftrightarrow> \<tau> \<^bold>\<Turnstile> (Ness\<^sub> {x} \<phi>)) \<longleftrightarrow> (Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x} \<phi>) = (Ness\<^sub> {x} \<phi>))" by (rule allE)
  hence"(Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x} \<phi>) = (Ness\<^sub> {x} \<phi>)" using a by simp
  thus ?thesis by simp
qed

lemma Corollary2: "\<lfloor>(\<^bold>[Ag\<^bold>]\<phi>) \<^bold>\<rightarrow> ((Could\<^sup>m\<^sup>i\<^sup>n\<^sub> {x} (\<^bold>\<not>\<phi>)) \<^bold>\<rightarrow> Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x} \<phi>)\<rfloor>"
proof - 
  from Proposition5 have "\<forall>G. G \<noteq> {} \<longrightarrow> \<lfloor>(\<^bold>[Ag\<^bold>]\<phi>) \<^bold>\<rightarrow> ((Could\<^sub> G (\<^bold>\<not>\<phi>)) \<^bold>\<rightarrow> (Ness\<^sub> G \<phi>))\<rfloor>" by simp
  hence a: "\<forall>G. G \<noteq> {} \<longrightarrow> \<lfloor>(\<^bold>[Ag\<^bold>]\<phi>) \<^bold>\<rightarrow> ((Could\<^sup>m\<^sup>i\<^sup>n\<^sub> G (\<^bold>\<not>\<phi>)) \<^bold>\<rightarrow> (Ness\<^sub> G \<phi>))\<rfloor>" by simp
  have "{x} \<noteq> {}" by simp
  hence b: "\<lfloor>(\<^bold>[Ag\<^bold>]\<phi>) \<^bold>\<rightarrow> ((Could\<^sup>m\<^sup>i\<^sup>n\<^sub> {x} (\<^bold>\<not>\<phi>)) \<^bold>\<rightarrow> (Ness\<^sub> {x} \<phi>))\<rfloor>" using a by presburger
  from NessEq have eq: "(Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x} \<phi>) = (Ness\<^sub> {x} \<phi>)" by -
  let ?d = "(Ness\<^sup>m\<^sup>i\<^sup>n\<^sub> {x} \<phi>)"
  let ?c = "(Ness\<^sub> {x} \<phi>)"
  have "\<forall>c d a b. \<lfloor>a \<^bold>\<rightarrow> (b \<^bold>\<rightarrow> c)\<rfloor> \<longrightarrow> d = c \<longrightarrow> \<lfloor>a \<^bold>\<rightarrow> (b \<^bold>\<rightarrow> d)\<rfloor>" by simp
  hence "\<forall> d a b. \<lfloor>a \<^bold>\<rightarrow> (b \<^bold>\<rightarrow> ?c)\<rfloor> \<longrightarrow> d = ?c \<longrightarrow> \<lfloor>a \<^bold>\<rightarrow> (b \<^bold>\<rightarrow> d)\<rfloor>" by (rule allE)
  hence "\<forall>a b. \<lfloor>a \<^bold>\<rightarrow> (b \<^bold>\<rightarrow> ?c)\<rfloor> \<longrightarrow> ?d = ?c \<longrightarrow> \<lfloor>a \<^bold>\<rightarrow> (b \<^bold>\<rightarrow> ?d)\<rfloor>" by (rule allE)
  hence "\<forall>a b. \<lfloor>a \<^bold>\<rightarrow> (b \<^bold>\<rightarrow> ?c)\<rfloor> \<longrightarrow> \<lfloor>a \<^bold>\<rightarrow> (b \<^bold>\<rightarrow> ?d)\<rfloor>" using eq by simp
  hence "\<forall>b. \<lfloor>(\<^bold>[Ag\<^bold>]\<phi>) \<^bold>\<rightarrow> (b \<^bold>\<rightarrow> ?c)\<rfloor> \<longrightarrow> \<lfloor>(\<^bold>[Ag\<^bold>]\<phi>) \<^bold>\<rightarrow> (b \<^bold>\<rightarrow> ?d)\<rfloor>" by (rule allE)
  hence "\<lfloor>(\<^bold>[Ag\<^bold>]\<phi>) \<^bold>\<rightarrow> ((Could\<^sup>m\<^sup>i\<^sup>n\<^sub> {x} (\<^bold>\<not>\<phi>)) \<^bold>\<rightarrow> ?c)\<rfloor> \<longrightarrow> \<lfloor>(\<^bold>[Ag\<^bold>]\<phi>) \<^bold>\<rightarrow> ((Could\<^sup>m\<^sup>i\<^sup>n\<^sub> {x} (\<^bold>\<not>\<phi>)) \<^bold>\<rightarrow> ?d)\<rfloor>" by (rule allE)
  thus ?thesis using b by auto
qed 


lemma Coresubs: "\<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> G \<phi>) \<longrightarrow> (Core \<phi> \<tau>) \<subseteq> G" by auto

lemma emptneq: "a \<noteq> b \<longrightarrow> \<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> {a} \<phi>) \<longrightarrow> \<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> {b} \<phi>) \<longrightarrow> (Core \<phi> \<tau>) = {}"
proof -
  {assume asm1: "a \<noteq> b"
    and asm2: "\<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> {a} \<phi>)"
    and asm3: "\<tau> \<^bold>\<Turnstile> (\<^bold>\<Delta>\<^sup>m\<^sup>i\<^sup>n\<^sub> {b} \<phi>)"
    hence "(Core \<phi> \<tau>) \<subseteq> {a} \<and> (Core \<phi> \<tau>) \<subseteq> {b}" using Coresubs asm2 asm3 by simp
    hence "(Core \<phi> \<tau>) = {}" using asm1 by blast}
  thus ?thesis by simp
qed

lemma memin: "(\<tau> ~ (G::\<mu> set) \<tau>b) \<longrightarrow> x \<in> G \<longrightarrow> \<tau>b \<in> (alt\<^sub> x \<tau>)" by blast

lemma inmem: "(\<forall>x \<in> G. \<tau>b \<in> (alt\<^sub> x \<tau>)) \<longrightarrow> (\<tau> ~ (G::\<mu> set) \<tau>b)" using tildeeqU by auto


lemma singletonacc: "(\<tau> ~ {x} \<tau>b) \<longleftrightarrow> ((\<tau>\<^bold>~(x::\<mu>)\<tau>b))" 
  using xsub by auto

lemma eqclassalt: "y \<in> alt\<^sub> x (\<tau>) \<longrightarrow> ((y::i)\<^bold>~(x::\<mu>)(z::i)) \<longrightarrow> z \<in> (alt\<^sub> x (\<tau>))"
  by (metis mem_Collect_eq tildexeq)

lemma eqclassalt2: "cla \<in> (\<^bold>A\<^sub> x) \<longrightarrow> y \<in> cla \<longrightarrow> ((y::i)\<^bold>~(x::\<mu>)(z::i)) \<longrightarrow> z \<in> cla" 
  using eqclassalt by blast

lemma eqclassalt3: "cla \<in> (\<^bold>A\<^sub> x) \<longrightarrow> y \<in> cla \<longrightarrow> z \<in> cla \<longrightarrow> ((y::i)\<^bold>~(x::\<mu>)(z::i))" using mem_Collect_eq tildexeq 
  by (smt (verit, del_insts))

lemma ac: "action \<in> (\<^bold>A\<^sub> x) \<longrightarrow> z \<in> action \<longrightarrow> y \<in> action \<longrightarrow> (z \<^bold>~x y)" 
  using eqclassalt3 by blast
lemma rac: "action \<in> (\<^bold>A\<^sub> x) \<longrightarrow> z \<in> action \<longrightarrow> (z \<^bold>~x y) \<longrightarrow> y \<in> action"
  using eqclassalt by blast

end