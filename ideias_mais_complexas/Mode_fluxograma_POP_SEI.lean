--Este é um prototipo que modela o Anexo I da Portaria normativa da Reitoria n°117/2023 da UFLA. Este Anexo corresponde ao Fluxograma do POP para Cadastro, Alteração ou Inativação de Tipos ou Modelos de Documento. O objetivo é analisar o rigor lógico da Portaria
Normativa

-- Tipos
inductive Acao where
  | iniciar | inserirProcesso | escolherCadastro | escolherAlteracao
  | escolherInativacao | incluirTipo| incluirMetadados
  | registrarAlteracao | anexarCopia | assinarEEnviar --troquei encaminharCDU por assinarEEnviar
  | analisarPedido | emitirAnuencia | emitirRecusa --| realizarAjustes | emitirDocumentoRetificador
  | cadastrarOuAlterarNoSEI | concluir
  deriving BEq, DecidableEq, Repr

inductive Role | unidadeUsuaria | autoridade | cdu_proplag --| sistema<---isso aqui não é usado
  deriving BEq, DecidableEq, Repr

inductive Unidade | unid_a | unid_b | unid_c
  deriving BEq, DecidableEq, Repr
--Tipo para identificar o setor da pessoa envolvida no processo (solicitante, responsável, etc...)

inductive Parecer | anuencia | recusa
  deriving BEq, DecidableEq, Repr

structure Estado where
  processoIniciado       : Bool := false
  processoInserido       : Bool := false
  acaoEscolhida          : Option Acao := none
  tipoIncluido           : Bool := false
  metadadosAtualizados   : Bool := false
  alteracaoRegistrada    : Bool := false
  copiaAnexada           : Bool := false
  enviadoAutoridade      : Bool := false --Trocado encaminhadoCDU         : Bool := false
  parecer                : Option Parecer := none
  analiseConcluida       : Bool := false
  --ajustesRealizados      : Bool := false
  --docRetificadorEmitido  : Bool := false
  cadastroFinalizado     : Bool := false
  processoConcluido      : Bool := false
  deriving Repr, DecidableEq

def estadoInicial : Estado := {}


structure Request where
  action : Acao
  actor  : Role
  unidade : Unidade := .unid_a
  deriving Repr, DecidableEq


structure Entities where
  state : Estado
  inSEI : Bool := false
  solicitante : Option Unidade := none
  responsavel : Option Unidade := none
  deriving Repr, DecidableEq

-- Motor de políticas
inductive Effect | permit | forbid deriving DecidableEq, Repr

-- Policy como registros com predicado booleano (compatível com native_decide)
structure Policy where
  id      : Nat
  effect  : Effect
  applies : Request → Entities → Option Bool

/-- `applies` devolve `Option Bool`. Isso significa que devolve três possibilidades
    * `some true`  → a regra se aplica
    * `some false` → a regra não se aplica
    * `none`       → a regra FALHOU (faltou informação para decidir) -/


def satisfied (p : Policy) (req : Request) (ent : Entities) : Prop :=
  p.applies req ent = some true

-- Obs.: mudamos o retorno para List Policy (em vez de List PolicyID)
-- para que a equivalência com HasSatisfiedEffect seja provável diretamente.
def satisfiedPolicies (e : Effect) (ps : List Policy) (req : Request) (ent : Entities) :
    List Policy :=
  ps.filter (fun p => p.effect = e && p.applies req ent = some true)

def errorPolicies (ps : List Policy) (req : Request) (ent : Entities) : List Policy :=
  ps.filter (fun p => (p.applies req ent).isNone)


inductive Decision | allow | deny deriving DecidableEq, Repr

structure Response where
  decision            : Decision
  determiningPolicies : List Policy
  erroringPolicies    : List Policy

def isAuthorized (req : Request) (ent : Entities) (ps : List Policy) : Response :=
  let forbids := satisfiedPolicies .forbid ps req ent
  let permits := satisfiedPolicies .permit ps req ent
  let errs    := errorPolicies ps req ent
  if forbids.isEmpty && !permits.isEmpty
  then { decision := .allow, determiningPolicies := permits, erroringPolicies := errs }
  else { decision := .deny,  determiningPolicies := forbids, erroringPolicies := errs }

def HasSatisfiedEffect (e : Effect) (req : Request) (ent : Entities)
    (ps : List Policy) : Prop :=
  ∃ p, p ∈ ps ∧ p.effect = e ∧ satisfied p req ent

def IsExplicitlyForbidden := HasSatisfiedEffect .forbid

--  Leis do motor de políticas

theorem satisfied_iff_satisfiedPolicies_non_empty
    {e : Effect} {req : Request} {ent : Entities} {ps : List Policy} :
    HasSatisfiedEffect e req ent ps ↔
      (satisfiedPolicies e ps req ent).isEmpty = false := by
  simp [HasSatisfiedEffect, satisfiedPolicies, satisfied]

theorem explicitly_forbidden_iff_satisfying_forbid
    {req : Request} {ent : Entities} {ps : List Policy} :
    IsExplicitlyForbidden req ent ps ↔
      (satisfiedPolicies .forbid ps req ent).isEmpty = false :=
  satisfied_iff_satisfiedPolicies_non_empty

theorem forbid_trumps_permit
    (req : Request) (ent : Entities) (ps : List Policy) :
    IsExplicitlyForbidden req ent ps →
      (isAuthorized req ent ps).decision = .deny := by
  intro h
  unfold isAuthorized
  rw [explicitly_forbidden_iff_satisfying_forbid] at h
  simp [h]

-- Máquina de estados do fluxograma
def passo (s : Estado) : Acao → Option Estado
  | .iniciar =>
      if s.processoIniciado then none
      else some { s with processoIniciado := true }
  | .inserirProcesso =>
      if s.processoIniciado && !s.processoInserido then
        some { s with processoInserido := true } else none
  | .escolherCadastro =>
      if s.processoInserido && s.acaoEscolhida.isNone then
        some { s with acaoEscolhida := some .escolherCadastro } else none
  | .escolherAlteracao =>
      if s.processoInserido && s.acaoEscolhida.isNone then
        some { s with acaoEscolhida := some .escolherAlteracao } else none
  | .escolherInativacao =>
      if s.processoInserido && s.acaoEscolhida.isNone then
        some { s with acaoEscolhida := some .escolherInativacao } else none
  | .incluirTipo =>
      if s.acaoEscolhida = some .escolherCadastro && !s.tipoIncluido then
        some { s with tipoIncluido := true } else none
  | .incluirMetadados =>
      if (s.acaoEscolhida = some .escolherCadastro ||
          s.acaoEscolhida = some .escolherAlteracao)
         && !s.metadadosAtualizados then
        some { s with metadadosAtualizados := true } else none
  | .registrarAlteracao =>
      if (s.metadadosAtualizados || s.acaoEscolhida = some .escolherInativacao)
         && !s.alteracaoRegistrada then
        some { s with alteracaoRegistrada := true } else none
  | .anexarCopia =>--O que se anexa não é uma cópia, é o modelo (o layout do documento, em PDF)
      if s.alteracaoRegistrada && !s.copiaAnexada then
        some { s with copiaAnexada := true } else none
    | .assinarEEnviar =>
      if (s.copiaAnexada || s.acaoEscolhida == some .escolherInativacao)
         && s.alteracaoRegistrada && !s.enviadoAutoridade then
        some { s with enviadoAutoridade := true } else none
  | .analisarPedido =>
      if s.enviadoAutoridade && !s.analiseConcluida then
        some { s with analiseConcluida := true } else none
  | .emitirAnuencia =>
      if s.analiseConcluida && s.parecer.isNone then
        some { s with parecer := some .anuencia } else none
  | .emitirRecusa =>
      if s.analiseConcluida && s.parecer.isNone then
        some { s with parecer := some .recusa, processoConcluido := true } else none
  | .cadastrarOuAlterarNoSEI =>
      if s.parecer == some .anuencia && !s.cadastroFinalizado then
        some { s with cadastroFinalizado := true } else none
  | .concluir =>
      if s.cadastroFinalizado && !s.processoConcluido then
        some { s with processoConcluido := true } else none

-- Políticas das raias do Anexo I
/-- Etapas da raia da direita (unidade solicitante). -/
def acoesDaSolicitante : List Acao :=
  [.iniciar, .inserirProcesso, .escolherCadastro, .escolherAlteracao,
   .escolherInativacao, .incluirTipo, .incluirMetadados,
   .registrarAlteracao, .anexarCopia, .assinarEEnviar]

/-- Etapas da raia do meio (autoridade da unidade responsável). -/
def acoesDaAutoridade : List Acao := [.analisarPedido, .emitirAnuencia, .emitirRecusa]

def policiesRaias : List Policy :=
  [ { id := 1, effect := .permit, applies := fun _ _ => some true }
  , { id := 2, effect := .forbid, applies := fun req _ =>
        some (acoesDaAutoridade.contains req.action && req.actor != .autoridade) }
  , { id := 3, effect := .forbid, applies := fun req _ =>
        some ([Acao.cadastrarOuAlterarNoSEI, .concluir].contains req.action
              && req.actor != .cdu_proplag) }
    /- regra 4: analisar e decidir só pela unidade dona do tipo de documento.
       Para as ações da autoridade, compara a unidade de quem pede com `ent.responsavel`:
         * responsável registrado (`some u`) → `some (req.unidade != u)`
         * responsável ausente (`none`)      → `none`: a regra FALHA
       Para as demais ações a regra não diz nada (`some false`), então não falha à toa. -/
  , { id := 4, effect := .forbid, applies := fun req ent =>
        if acoesDaAutoridade.contains req.action then
          ent.responsavel.map (fun u => req.unidade != u)
        else some false }
    /- regra 5: as etapas da raia da direita só pela unidade solicitante.
       Mesmo padrão da regra 4, comparando com `ent.solicitante`. -/
  , { id := 5, effect := .forbid, applies := fun req ent =>
        if acoesDaSolicitante.contains req.action then
          ent.solicitante.map (fun u => req.unidade != u)
        else some false } ]


def passoAutorizado (ps : List Policy) (req : Request) (ent : Entities)
    (s : Estado) (a : Acao) : Option Estado :=
  match passo s a with
  | none      => none
  | some s'   =>
      match (isAuthorized req ent ps).decision with
      | .allow => some s'
      | .deny  => none

/-- **Teorema central**: uma ação explicitamente proibida nunca transita, independentemente de satisfazer ou não as pré-condições de `passo`. -/
theorem forbidden_blocks_step
    {ps : List Policy} {req : Request} {ent : Entities}
    {s : Estado} {a : Acao}
    (h : IsExplicitlyForbidden req ent ps) :
    passoAutorizado ps req ent s a = none := by
  unfold passoAutorizado
  have h_deny := forbid_trumps_permit req ent ps h
  cases hp : passo s a with
  | none    => rfl
  | some s' => rw [h_deny]

/-- Complementar: `allow` garante ausência de forbid. -/
theorem allow_means_no_forbid
    {req : Request} {ent : Entities} {ps : List Policy}
    (h : (isAuthorized req ent ps).decision = .allow) :
    ¬ IsExplicitlyForbidden req ent ps := by
  intro hf
  have hd := forbid_trumps_permit req ent ps hf
  rw [h] at hd
  cases hd

-- Caminho autorizado: uma etapa proibida derruba o caminho
def caminhoAutorizado (ps : List Policy) (reqs : List Request) (ent : Entities)
    (s : Estado) (acoes : List Acao) : Option Estado :=
  match acoes, reqs with
  | [],      _      => some s
  | a :: as, r :: rs =>
      match passoAutorizado ps r ent s a with
      | none     => none
      | some s'  => caminhoAutorizado ps rs ent s' as
  | _ :: _,  []     => none

theorem forbidden_any_step_fails
    {ps : List Policy} {ent : Entities} {s : Estado}
    {a : Acao} {as : List Acao} {r : Request} {rs : List Request}
    (h : IsExplicitlyForbidden r ent ps) :
    caminhoAutorizado ps (r :: rs) ent s (a :: as) = none := by
  unfold caminhoAutorizado
  rw [forbidden_blocks_step h]

