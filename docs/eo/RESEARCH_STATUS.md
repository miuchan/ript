# Esplora stato

[English](../en/RESEARCH_STATUS.md) · [简体中文](../zh-CN/RESEARCH_STATUS.md) ·
[日本語](../ja/RESEARCH_STATUS.md) · [Esperanto](RESEARCH_STATUS.md)

Ĉi tiu paĝo estas konciza esplormapo, ne la teorema registro. Ekzaktaj tipoj,
dependecoj, fontoj kaj supozoj troviĝas en la [formala plano](reference/BLUEPRINT.md)
kaj la [aksioma inventaro](reference/AXIOMS.md).

## Statusvortoj

- `DEFINED` — interfaco aŭ konstruo ekzistas;
- `STATEMENT_FORMALIZED` — teorema tipo ekzistas, sed pruvo ne estas postulata;
- `PROVED` — Lean akceptas la pruvon sen projektaj aksiomoj aŭ pruvtruoj;
- `BLOCKED` — specifa manko de dependeco aŭ API estas registrita;
- `OPEN_RESEARCH` — la aserto aŭ ĝusta formulo restas esplora.

La README kaj modelmatrico resumas nur realigitan, kompilitan laboron.

## Realigitaj kolonoj

### Rimed-sentema sintakso kaj semantiko

La seria kaj simetria monoida kerno enhavas ruleblan sintakson, sintaksan
koston, interpretojn, eksplicitajn derivojn, validecon, termmodelojn, relativan
kompletecon kaj monoidan komencecon. Kostfunkcioj kaj atingitaj buĝetfiltradoj
havas pruvitajn ir-revenajn leĝojn sub eksplicitaj kondiĉoj.

La sama monoida lingvo povas esti puŝita laŭ ordigita adicia rimedmapo sen
ŝanĝi dratojn aŭ generatorojn. La esprimtraduko estas komputebla kaj inversebla;
heterogena interpreto estas ekzakte reprezentata per ordinara interpreto de la
puŝita signaturo; taksado obeas la tradukitan buĝeton; la libera modelo estas
relative kompleta kaj ekzakte realigas la tradukitan koston.

La unua konkreta intermodela tranĉo ankaŭ kompiliĝas. Unu unu-kosta Bulea
turna signaturo estas interpretita per ekzakta probabla negacio, Pauli-X-a
kvantuma evoluo, finia kaŭza mekanismo, plurdimensia komputado, task-rilata
semantika informo kaj Gibbs-konserva termika procezo. Unu kerne kontrolita
teoremo pakas la ses observeblajn limajn ekvaciojn. Komputado retenas sian
indiĝenan vektoran rimedon; kvantumaj kaj termikaj analizaj observaĵoj restas
apartaj de la nula abstrakta kosto de ĉi tiu tranĉo.

### Ekzakta finia probablo kaj decido

Normaligitaj racionalaj stokastaj kanaloj formas kategorion kun tensoro,
konveksaj miksaĵoj, kopio kaj forĵeto. La finia-distribua Kleisli-reprezento kaj
fidela finia ponto al Mathlib `Stoch` kompiliĝas. La decida tavolo enhavas
Blackwell-monotonecon, finiajn inversajn rezultojn kun la necesa ne-malplena
kaŝstata limo, kaj ekzaktajn apartigajn atestilojn.

### Kaŭzaj, komputaj kaj termikaj modeloj

Finiaj DAG-modeloj havas normaligitan observan semantikon kaj malmolajn
intervenojn. Totala kaj `Option`-parta komputado spuras formalajn paŝojn,
demandojn, memoron kaj pordojn. Finiaj Gibbs-konservaj modeloj ligas ekzaktajn
racionalajn operaciojn al KL, libera energio, korelacio, proksimuma viŝado kaj
eksplicitaj Landauer-atestantoj sub deklaritaj analizaj kondiĉoj.

### Finiaj kvantumaj kanaloj

Finiaj Kraus-familioj fariĝas kanaloj nur post pruvoj de pozitiveco kaj
spuro-konservo. Identeco, komponado, tensoro, spura forĵeto, kompleta pozitiveco
sub finia pligrandigo kaj fidela klasika senfaziga enigo kompiliĝas. Neniu
universala kvantuma kopiado estas postulata.

### Modeloj kiel pli altaj objektoj

Rimed-indeksitaj simetriaj monoidaj procezmodeloj, rimed-nepligrandigaj fortaj
plektitaj monoidaj funktoroj kaj monoidaj naturaj transformoj formas
bikategorion. Kost-ekzaktaj ekvivalentoj registras nombran reflektadon. Ordinara
homotopia lokalizado kaj pluraj irantaj lokalizaj ekzemploj kompiliĝas.

Malsamaj rimedalgebroj nun estas ligeblaj per ordigitaj adiciaj homomorfioj.
Seriaj, paralelaj, strukturaj kaj buĝetaj leĝoj reindeksiĝas, kaj heterogenaj
fortaj modelmorfismoj komponiĝas kun la rimedmapoj. La fibroj formas totalan
bikategorion: objektoj enhavas rimedalgebron kaj modelon, 1-ĉeloj enhavas
rimedtradukon kaj fortan modelmapon, kaj 2-ĉeloj enhavas egalecon de la
rimedtraduko kun monoida natura transformo. Horizontala komponado, interŝanĝo,
asociiloj, unuigiloj, kvinangulo kaj triangulo estas kompilitaj.

### Limigita interna univalenta tavolo

Profunda sintakso distingas internan identecon de struktura ekvivalento kaj
interpretas ambaŭ sen eksteraj aksiomoj. La kompilita semantiko enhavas
grupoidon, objektkvocienton, skeleton, Yoneda-envolvaĵon, Kan-simplician nervon
kaj klasifikan diagramon kun la eksplicita grupa complete-Segal-interfaco.

## Aktiva esplorfronto

La celo estas komputebla, maŝine kontrolebla, univalenta kaj pli-alt-kategoria
teorio de rimed-limigitaj informprocezoj, en kiu klasika probablo, kvantumaj
procezoj, kaŭzaj modeloj, komputado, semantika informo kaj termodinamiko estas
ligitaj per pruvitaj reprezentaj kaj kompletecaj teoremoj.

La unua totala pli alta kategorio super variaj rimedalgebroj enhavas:

- ordigitan adician reindeksadon de procezaj, paralelaj, strukturaj kaj
  pruv-portantaj buĝetaj leĝoj;
- rimedŝanĝajn funktorojn, identecan kongruon, komponadon kaj buĝettransporton;
- reindeksitajn `ProcessModel`-objektojn kaj heterogenajn fortajn modelmapojn;
- monoidajn 2-ĉelojn kaj lokajn kategoriojn super fiksaj rimedtradukoj;
- totalajn modelobjektojn, heterogenan horizontalan komponadon, flankkomponadon,
  interŝanĝon, asociilojn, unuigilojn, kvinangulon kaj triangulon;
- komunan monoidan sintakson kun kosttraduko al indiĝenaj rimedalgebroj,
  inversebla esprimtraduko, ekzakta reprezenta teoremo kaj tradukita libera-modela
  kompleteco;
- unu efektivan Bulean turnan signaturon kun ses modelspecifaj interpretoj kaj
  kerne kontrolita intermodela kongrua teoremo;
- ruleblan projekcion de `Fin 4 → Nat` al la unuopa `Nat`-paŝa koordinato.

La sekvaj teoremportaj tavoloj estas:

- etendi la unuan ses-modelan Bulean tranĉon al komuna kompona signaturo, kiu
  montras la probablajn, kaŭzajn, semantikajn, kvantumajn kaj termikajn
  diferencojn kun eksplicitaj analizaj kaj finiaj kondiĉoj;
- pruvi modelspecifajn reprezentajn, konservemajn kaj kompletecajn teoremojn,
  poste verajn intermodelajn komparojn;
- ligi la totalan modelbikategorion al interna univalenta kaj simplicia
  semantiko sen enigi nekomputeblajn kvocientajn elektojn en ruleblajn modelojn.

La parametrigita iranta lokalizado restas aktiva flanktemo. Ĝia arbitra levo
havas kompilitajn objektojn, 1-/2-ĉelojn, identecon, komponilon, naturecon,
unuigajn leĝojn, antaŭan asociecon kaj unu inversa/konservita/konservita branĉon.
Dek inversaj aŭ nuligaj finpunktsekvoj, pseŭdofunktora pakaĵo kaj la fina
nedisigebla esenca faktorigo restas malfermaj; plena bikategoria lokalizado ne
estas postulata.

## Eksplicite malferma aŭ ekster la amplekso

- ĝeneralaj mezurebl-spacaj kaŭzaj modeloj kaj kompleteco de do-kalkulo;
- identigo de formalaj paŝoj kun murhora tempo aŭ aparata kosto;
- neracionalaj reelaj probabloj en la rulebla finia kerno;
- universala kvantuma kopio;
- ekstera univalenteco por Lean-tipoj;
- Mathlib-denaska norma complete-Segal-spaco bazita sur kompleta malforta
  ekvivalento aŭ Quillen-modela API;
- plena Dwyer–Kan, simplicia, Rezk aŭ bikategoria lokalizado de la
  rimed-proceza bikategorio.

Nepruvitaj asertoj apartenas al la [registro de konjektoj](reference/CONJECTURES.md),
ne al Lean-aksiomoj aŭ teoremoj.

## Kie kontroli aserton

- modela operacio aŭ kapablo: [modelkapabla matrico](reference/MODEL_MATRIX.md)
- teorema tipo kaj dependecoj: [formala plano](reference/BLUEPRINT.md)
- kernaj supozoj: [aksioma inventaro](reference/AXIOMS.md)
- malferma esploro: [registro de konjektoj](reference/CONJECTURES.md)
- rulebla konduto: `Ript/Examples/` kaj `scripts/check-examples.sh`
- kunfanda preteco: `./scripts/quality-gate.sh`
