/* =====================================================================
 * Open_ScopeA.mch  --  Scope A: OPEN Policy-Mediation (B classic / AMN)
 *
 * Usable in BOTH:
 *   - Atelier B  : automatic proof of INVARIANT preservation POs
 *   - ProB       : model checking (invariant + deadlock) & animation
 *
 * AUTO-PROOF DESIGN (keeps Atelier B's ml/pp force-0/1 closing POs):
 *   * All state variables typed over finite enumerated SETS.
 *   * Every operation is a deterministic substitution under a PRE.
 *   * State-dependent invariants are implications whose antecedent is
 *     re-established by the operation's precondition  -> trivial PO.
 *   * No cardinality arithmetic, no nested quantifiers  -> no WD debt.
 *
 * Requirement traceability (Table 1):
 *   OPN-03/18  card life-cycle     OPN-17   CCM concurrency
 *   OPN-07     SD requests, OPEN executes   OPN-01/13 single writer
 *   OPN-20/22  token / deny-list            OPN-21   authorized mgmt
 * ===================================================================== */
MACHINE
    re_OPEN

SETS
    CARD_LCS  = {OP_READY, INITIALIZED, SECURED, CARD_LOCKED, TERMINATED};
    APP_LCS   = {APP_INSTALLED, APP_SELECTABLE, APP_SPECIFIC,
                 LOCKED_FROM_INSTALLED, LOCKED_FROM_SELECTABLE,
                 LOCKED_FROM_APPSPEC, APP_DELETED};
    CCM_STATE = {CCM_IDLE, CCM_BUSY};
    MGMT_MODE = {AUTHORIZED, DELEGATED};
    DECISION  = {ALLOW, DENY};
    LOCK_REQ  = {BY_ASSOC_SD, BY_GLOBALLOCK, BY_APP_SELF};   /* who may request LOCK */
    APP_ID    = {a1, a2}        /* finite: ProB explores exhaustively */

DEFINITIONS
    /* card states where content-management is permitted (OPN-18 sink) */
    CM_OK == {OP_READY, INITIALIZED, SECURED}

ABSTRACT_VARIABLES
    card_lcs, ccm, registry, app_lcs,
    pending, req_mode, token_ok, last_decision

INVARIANT
    /* ---- typing (trivial POs) ---- */
    card_lcs      : CARD_LCS                         &
    ccm           : CCM_STATE                        &
    registry      <: APP_ID                          &
    app_lcs       : registry --> APP_LCS             &
    pending       <: registry                        &
    req_mode      : pending --> MGMT_MODE            &
    token_ok      : pending --> BOOL                 &
    last_decision : DECISION                         &

    /* ---- OPN-18: no content-mgmt when CARD_LOCKED / TERMINATED ---- */
    ( card_lcs /: CM_OK  =>  ccm = CCM_IDLE )        &

    /* ---- OPN-21/22: an AUTHORIZED pending request is pre-trusted ---- */
    ( !aa . ( aa : pending & req_mode(aa) = AUTHORIZED
                 => token_ok(aa) = TRUE ) )

INITIALISATION
    card_lcs      := OP_READY   ||
    ccm           := CCM_IDLE   ||
    registry      := {}         ||
    app_lcs       := {}         ||
    pending       := {}         ||
    req_mode      := {}         ||
    token_ok      := {}         ||
    last_decision := ALLOW

OPERATIONS

    /* ---------------- CARD LIFE-CYCLE (OPN-03, OPN-18) ---------------- */

    card_progress_init =
        PRE card_lcs = OP_READY & ccm = CCM_IDLE THEN
            card_lcs := INITIALIZED
        END;

    card_secure =
        PRE card_lcs = INITIALIZED & ccm = CCM_IDLE THEN
            card_lcs := SECURED
        END;

    card_lock =
        PRE card_lcs = SECURED & ccm = CCM_IDLE THEN
            card_lcs := CARD_LOCKED
        END;

    card_unlock =
        PRE card_lcs = CARD_LOCKED THEN
            card_lcs := SECURED
        END;

    card_terminate =
        PRE card_lcs /= TERMINATED & ccm = CCM_IDLE THEN
            card_lcs := TERMINATED
        END;

    /* ---------------- CCM CONCURRENCY (OPN-17) ---------------- */

    ccm_start =
        PRE ccm = CCM_IDLE & card_lcs : CM_OK THEN
            ccm := CCM_BUSY
        END;

    ccm_end =
        PRE ccm = CCM_BUSY THEN
            ccm := CCM_IDLE
        END;

    /* ---------------- SD REQUESTS (OPN-07, OPN-21/22) ---------------- */

    sd_request_authorized(aa) =
        PRE aa : registry & aa /: pending THEN
            pending  := pending \/ {aa}      ||
            req_mode(aa) := AUTHORIZED        ||
            token_ok(aa) := TRUE
        END;

    sd_request_delegated(aa) =
        PRE aa : registry & aa /: pending THEN
            pending  := pending \/ {aa}      ||
            req_mode(aa) := DELEGATED         ||
            token_ok(aa) := FALSE
        END;

    open_verify_token(aa) =
        PRE aa : pending & req_mode(aa) = DELEGATED & token_ok(aa) = FALSE THEN
            token_ok(aa) := TRUE
        END;

    /* ---------------- OPEN EXECUTES : single writer (OPN-01/13) ---------------- */

    open_register_new(aa) =
        PRE aa : APP_ID & aa /: registry & ccm = CCM_BUSY THEN
            registry := registry \/ {aa}      ||
            app_lcs(aa) := APP_INSTALLED
        END;

    /* INSTALLED -> SELECTABLE : installed & functional & req_by(AM v DM) */
    open_install(aa) =
        PRE aa : pending & token_ok(aa) = TRUE & ccm = CCM_BUSY
            & app_lcs(aa) = APP_INSTALLED THEN
            app_lcs(aa)   := APP_SELECTABLE   ||
            last_decision := ALLOW            ||
            pending       := pending - {aa}   ||
            req_mode      := {aa} <<| req_mode ||
            token_ok      := {aa} <<| token_ok
        END;

    /* SELECTABLE <-> Application-specific : APP_STATE [req_by(App_self)] */
    app_enter_specific(aa) =
        PRE aa : registry & ccm = CCM_BUSY & app_lcs(aa) = APP_SELECTABLE THEN
            app_lcs(aa) := APP_SPECIFIC
        END;

    app_leave_specific(aa) =
        PRE aa : registry & ccm = CCM_BUSY & app_lcs(aa) = APP_SPECIFIC THEN
            app_lcs(aa) := APP_SELECTABLE
        END;

    /* ---- LOCK / UNLOCK : the LOCKED-from-* states remember the origin ---- */

    /* INSTALLED -> LOCKED-from-INSTALLED : LOCK [req_by(assoc_SD v GlobalLock)] */
    app_lock_from_installed(aa, who) =
        PRE aa : registry & ccm = CCM_BUSY & app_lcs(aa) = APP_INSTALLED
            & who : {BY_ASSOC_SD, BY_GLOBALLOCK} THEN
            app_lcs(aa) := LOCKED_FROM_INSTALLED
        END;

    app_unlock_to_installed(aa, who) =
        PRE aa : registry & ccm = CCM_BUSY & app_lcs(aa) = LOCKED_FROM_INSTALLED
            & who : {BY_ASSOC_SD, BY_GLOBALLOCK} THEN
            app_lcs(aa) := APP_INSTALLED
        END;

    /* SELECTABLE -> LOCKED-from-SELECTABLE : LOCK [req_by(assoc_SD v GlobalLock v App_self)] */
    app_lock_from_selectable(aa, who) =
        PRE aa : registry & ccm = CCM_BUSY & app_lcs(aa) = APP_SELECTABLE
            & who : {BY_ASSOC_SD, BY_GLOBALLOCK, BY_APP_SELF} THEN
            app_lcs(aa) := LOCKED_FROM_SELECTABLE
        END;

    app_unlock_to_selectable(aa, who) =
        PRE aa : registry & ccm = CCM_BUSY & app_lcs(aa) = LOCKED_FROM_SELECTABLE
            & who : {BY_ASSOC_SD, BY_GLOBALLOCK} THEN
            app_lcs(aa) := APP_SELECTABLE
        END;

    /* Application-specific -> LOCKED-from-app-specific : LOCK [req_by(assoc_SD v GlobalLock v App_self)] */
    app_lock_from_appspec(aa, who) =
        PRE aa : registry & ccm = CCM_BUSY & app_lcs(aa) = APP_SPECIFIC
            & who : {BY_ASSOC_SD, BY_GLOBALLOCK, BY_APP_SELF} THEN
            app_lcs(aa) := LOCKED_FROM_APPSPEC
        END;

    app_unlock_to_appspec(aa, who) =
        PRE aa : registry & ccm = CCM_BUSY & app_lcs(aa) = LOCKED_FROM_APPSPEC
            & who : {BY_ASSOC_SD, BY_GLOBALLOCK} THEN
            app_lcs(aa) := APP_SPECIFIC
        END;

    /* ---- DELETE from any non-deleted state : req_by(OPEN, authorized) ---- */
    open_delete(aa) =
        PRE aa : registry & aa /: pending & ccm = CCM_BUSY
            & app_lcs(aa) /= APP_DELETED THEN
            app_lcs(aa) := APP_DELETED
        END;

    open_deny_denylisted(aa) =
        PRE aa : pending & req_mode(aa) = DELEGATED & token_ok(aa) = FALSE THEN
            last_decision := DENY             ||
            pending       := pending - {aa}   ||
            req_mode      := {aa} <<| req_mode ||
            token_ok      := {aa} <<| token_ok
        END;

    /* ---------------- TERMINAL SELF-LOOP (OPN-18) ----------------
     * TERMINATED is an intentional, legitimate final state. Modelling a
     * skip self-transition here means ProB no longer reports TERMINATED as
     * a deadlock, so "Find Deadlocks" now flags ONLY unintended deadlocks
     * (any dead state with card_lcs /= TERMINATED). The PO for this op is
     * trivial (skip preserves every invariant), so Atelier B auto-closes it.
     */
    terminated_end =
        PRE card_lcs = TERMINATED THEN
            skip
        END

END
