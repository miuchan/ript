# Projekta amplekso kaj fidolimoj

[English](../en/PROJECT_SCOPE.md) · [简体中文](../zh-CN/PROJECT_SCOPE.md) ·
[日本語](../ja/PROJECT_SCOPE.md) · [Esperanto](PROJECT_SCOPE.md)

Ĉi tiu paĝo klarigas kion Ript celas formaligi, kiel ĝiaj asertoj estas
kontrolataj, kaj kiuj projektaj limoj validas.

## Celo

Ordinaraj procezteorioj priskribas kiuj tipitaj procezoj komponiĝas. Rimeda
teorio devas ankaŭ specifi kiel kostoj komponiĝas, kiuj reskriboj konservas ilin,
kaj kiam sintaksaj taksoj estas semantike validaj. Ript eksplicitigas tiujn
devojn en Lean.

La reganta esplorcelo estas konstrui komputeblan, maŝine kontroleblan,
univalentan kaj pli-alt-kategorian teorion de rimed-limigitaj informprocezoj, en
kiu klasika probablo, kvantumaj procezoj, kaŭzaj modeloj, komputado, semantika
informo kaj termodinamiko estas malsamaj modeloj kun reprezentaj kaj
kompletecaj teoremoj. Maturecaj avizoj markas kio restas nepruvita; ili ne
malgrandigas la celon.

La biblioteko sekvas kvin principojn:

- ordigitaj adiciaj rimedoj spuras seriajn kaj paralelajn buĝetojn;
- rulebla sintakso restas aparta de kvocientaj pruvmodeloj;
- interpretoj pruvas konservon de tipoj, ekvacioj kaj rimedlimoj;
- tensoro, kopio, forĵeto, konvekseco, kaŭzeco kaj termodinamiko estas
  sendependaj kapabloj;
- teoremaj asertoj estas limigitaj al deklaroj kompilitaj per la fiksita ilĉeno.

Ript estas formala esplorbiblioteko, ne rultempa taksilo aŭ jam kompleta teorio
de fizika informo. La preciza limo troviĝas en [Esplora stato](RESEARCH_STATUS.md).

## Enhavo de la deponejo

La kerno kovras kostitajn kategoriojn, ruleblajn seriajn kaj monoidajn
sintaksojn, interpretojn, validecon, relativan kompletecon kaj monoidan
komencecon. Finiaj modeloj kovras determinismajn kaj stokastajn kanalojn,
decidproblemojn, totalan kaj partan komputadon, kaŭzajn DAG-ojn, termikajn
sistemojn kaj finiajn kvantumajn kanalojn.

Pli altaj tavoloj organizas modelojn en bikategorion, difinas kost-ekzaktajn
ekvivalentojn, esploras irantajn lokalizadojn kaj donas limigitan internan
identec-semantikon. Ordigitaj adiciaj rimedŝanĝoj ligas malsamajn rimedalgebrojn
en totalan bikategorion. La [modelkapabla matrico](reference/MODEL_MATRIX.md)
registras nur realigitajn kaj kompilitajn operaciojn.

La plej alta kompilita lokaliza tavolo nun donas plenan generitan hammock-
prezenton de ĉiu loka mapkategorio, rektajn kategoria-nervajn ekvivalentojn al
la faktaj lokalizaj celoj, eksplicitajn simpliciajn homotopiajn inversojn kaj
finiĝantan semantik-konservan administran redukton. Tio estas auditita
projekta Dwyer--Kan-kerno, ne ankoraŭ komparo kun la klasika reduktita arbitra-
krada hammock aŭ norma tutmonda Rezk-malforta ekvivalento.

## Fidmodelo

Ript malpermesas:

- pruvtruojn kiel `sorry` kaj `admit`;
- projektajn aksiomojn anstataŭ nefinita esploro;
- eviton de kompilila fido kaj nesekurajn bibliotekajn deklarojn;
- nedokumentitajn supozojn en audititaj ĉefaj teoremoj.

La kvalita kontrolo fiksas Lean kaj Mathlib, traktas avertojn kiel erarojn,
rulas reprezentajn modelojn, kontrolas fontregulojn kaj supozojn, kaj faras
plenan konstruon. Vidu la [aksioman inventaron](reference/AXIOMS.md) kaj la
[registron de konjektoj](reference/CONJECTURES.md).

Kerna kontrolo certigas, ke deklaro sekvas el siaj listigitaj supozoj. Ĝi ne
mem validigas la empirian taŭgecon de formala fizika modelo.

## Matureco kaj stabileco

- la Lake-pakaĵa versio estas `0.1.0`;
- ne ekzistas stabila publika API aŭ etikeda kongruecpromeso;
- ne ekzistas arkiva DOI;
- teoremnomoj kaj modullimoj povas ŝanĝiĝi dum la esploro.

Por reprodukteblo fiksu plenan commit-SHA kaj citu la deponejon kun tiu SHA.

## Permesilo

Neniu liberfonta permesilo ankoraŭ estas elektita. Publika haveblo de la fonto
ne donas permeson kopii, modifi aŭ redistribui ĝin. Formala permesilo anstataŭos
ĉi tiun tekston se la projekto elektos unu.

## Aŭtoritataj registroj

- [Esplora stato](RESEARCH_STATUS.md)
- [Formala plano](reference/BLUEPRINT.md)
- [Aksioma inventaro](reference/AXIOMS.md)
- [Registro de konjektoj](reference/CONJECTURES.md)
- [Kontribua gvidilo](CONTRIBUTING.md)
- [Regado](GOVERNANCE.md)
- [Sekureco](SECURITY.md)
