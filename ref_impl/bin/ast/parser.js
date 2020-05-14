"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const parser_env_1 = require("./parser_env");
const type_signature_1 = require("./type_signature");
const body_1 = require("./body");
const assembly_1 = require("./assembly");
const KeywordStrings = [
    "pragma",
    "hidden",
    "factory",
    "virtual",
    "abstract",
    "override",
    "entrypoint",
    "recursive?",
    "recursive",
    "_debug",
    "abort",
    "assert",
    "case",
    "check",
    "concept",
    "const",
    "elif",
    "else",
    "enum",
    "entity",
    "ensures",
    "false",
    "field",
    "fn",
    "from",
    "function",
    "global",
    "identifier",
    "if",
    "invariant",
    "method",
    "namespace",
    "none",
    "or",
    "provides",
    "ref",
    "return",
    "requires",
    "xrequires",
    "static",
    "switch",
    "true",
    "type",
    "typedef",
    "unique",
    "using",
    "var",
    "when",
    "where",
    "yield",
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : a.localeCompare(b); });
const SymbolStrings = [
    "[",
    "(",
    "{",
    "]",
    ")",
    "}",
    "{|",
    "|}",
    "#",
    "&",
    "&&",
    "@",
    "!",
    "!=",
    ":",
    "::",
    ",",
    ".",
    "...",
    "=",
    "==",
    "=>",
    "==>",
    ";",
    "|",
    "||",
    "+",
    "*",
    "/",
    "%",
    "?",
    "?&",
    "?|",
    "?.",
    "<",
    "<=",
    ">",
    ">=",
    "-",
    "->",
    "?->"
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : a.localeCompare(b); });
const LeftScanParens = ["[", "(", "{", "{|"];
const RightScanParens = ["]", ")", "}", "|}"];
const AttributeStrings = ["hidden", "factory", "virtual", "abstract", "override", "entrypoint", "recursive", "recursive?"];
const SpecialInvokeNames = ["update", "merge", "project", "difference"];
const TokenStrings = {
    Clear: "[CLEAR]",
    Error: "[ERROR]",
    Int: "[LITERAL_INT]",
    String: "[LITERAL_STRING]",
    TypedString: "[LITERAL_TYPED_STRING]",
    //Names
    Namespace: "[NAMESPACE]",
    Type: "[TYPE]",
    Template: "[TEMPLATE]",
    Identifier: "[IDENTIFIER]",
    EndOfStream: "[EOS]"
};
class Token {
    constructor(line, column, cpos, span, kind, data) {
        this.line = line;
        this.column = column;
        this.pos = cpos;
        this.span = span;
        this.kind = kind;
        this.data = data;
    }
}
class SourceInfo {
    constructor(line, column, cpos, span) {
        this.line = line;
        this.column = column;
        this.pos = cpos;
        this.span = span;
    }
}
exports.SourceInfo = SourceInfo;
class Lexer {
    constructor(input) {
        this.m_input = input;
        this.m_internTable = new Map();
        this.m_cline = 1;
        this.m_linestart = 0;
        this.m_cpos = 0;
        this.m_tokens = [];
    }
    static findSymbolString(str) {
        return SymbolStrings.find((value) => str.startsWith(value));
    }
    static findKeywordString(str) {
        let imin = 0;
        let imax = KeywordStrings.length;
        while (imin < imax) {
            const imid = Math.floor((imin + imax) / 2);
            const scmpval = (str.length !== KeywordStrings[imid].length) ? (KeywordStrings[imid].length - str.length) : str.localeCompare(KeywordStrings[imid]);
            if (scmpval === 0) {
                return KeywordStrings[imid];
            }
            else if (scmpval < 0) {
                imax = imid;
            }
            else {
                imin = imid + 1;
            }
        }
        return undefined;
    }
    ////
    //Helpers
    static isNamespaceName(str) {
        return /^NS/.test(str);
    }
    static isTypenameName(str) {
        return str.length > 1 && !/^NS/.test(str) && /^[A-Z]/.test(str);
    }
    static isTemplateName(str) {
        return str.length === 1 && /^[A-Z]$/.test(str);
    }
    static isIdentifierName(str) {
        return /^[a-z_]/.test(str);
    }
    recordLexToken(epos, kind) {
        this.m_tokens.push(new Token(this.m_cline, this.m_cpos - this.m_linestart, this.m_cpos, epos - this.m_cpos, kind, kind)); //set data to kind string
        this.m_cpos = epos;
    }
    recordLexTokenWData(epos, kind, data) {
        const rdata = this.m_internTable.get(data) || this.m_internTable.set(data, data).get(data);
        this.m_tokens.push(new Token(this.m_cline, this.m_cpos - this.m_linestart, this.m_cpos, epos - this.m_cpos, kind, rdata));
        this.m_cpos = epos;
    }
    tryLexWS() {
        Lexer._s_whitespaceRe.lastIndex = this.m_cpos;
        const m = Lexer._s_whitespaceRe.exec(this.m_input);
        if (m === null) {
            return false;
        }
        for (let i = 0; i < m[0].length; ++i) {
            if (m[0][i] === "\n") {
                this.m_cline++;
                this.m_linestart = this.m_cpos + i + 1;
            }
        }
        this.m_cpos += m[0].length;
        return true;
    }
    tryLexComment() {
        Lexer._s_commentRe.lastIndex = this.m_cpos;
        const m = Lexer._s_commentRe.exec(this.m_input);
        if (m === null) {
            return false;
        }
        if (m.groups) {
            const groups = m.groups;
            if (groups.multiline !== undefined) {
                for (const char of groups.multiline) {
                    if (char === "\n") {
                        this.m_cline++;
                    }
                }
            }
            if (groups.multilineEndChar !== undefined && groups.multilineEndChar !== "/") {
                this.recordLexToken(this.m_cpos, TokenStrings.Error);
            }
        }
        this.m_cpos += m[0].length;
        return true;
    }
    tryLexNumber() {
        Lexer._s_numberRe.lastIndex = this.m_cpos;
        const m = Lexer._s_numberRe.exec(this.m_input);
        if (m === null) {
            return false;
        }
        this.recordLexTokenWData(this.m_cpos + m[0].length, TokenStrings.Int, m[0]);
        return true;
    }
    tryLexString() {
        Lexer._s_stringRe.lastIndex = this.m_cpos;
        const ms = Lexer._s_stringRe.exec(this.m_input);
        if (ms !== null) {
            this.recordLexTokenWData(this.m_cpos + ms[0].length, TokenStrings.String, ms[0]);
            return true;
        }
        Lexer._s_typedStringRe.lastIndex = this.m_cpos;
        const mts = Lexer._s_typedStringRe.exec(this.m_input);
        if (mts !== null) {
            this.recordLexTokenWData(this.m_cpos + mts[0].length, TokenStrings.TypedString, mts[0]);
            return true;
        }
        return false;
    }
    tryLexSymbol() {
        Lexer._s_symbolRe.lastIndex = this.m_cpos;
        const m = Lexer._s_symbolRe.exec(this.m_input);
        if (m === null) {
            return false;
        }
        const sym = Lexer.findSymbolString(m[0]);
        if (sym === undefined) {
            return false;
        }
        else {
            this.recordLexToken(this.m_cpos + sym.length, sym);
            return true;
        }
    }
    tryLexName() {
        if (this.m_input.startsWith("recursive?", this.m_cpos)) {
            this.recordLexToken(this.m_cpos + "recursive?".length, "recursive?");
            return true;
        }
        Lexer._s_nameRe.lastIndex = this.m_cpos;
        const m = Lexer._s_nameRe.exec(this.m_input);
        if (m === null) {
            return false;
        }
        const name = m[0];
        const kwmatch = Lexer.findKeywordString(name);
        if (kwmatch) {
            this.recordLexToken(this.m_cpos + name.length, kwmatch);
            return true;
        }
        else if (Lexer.isNamespaceName(name)) {
            this.recordLexTokenWData(this.m_cpos + name.length, TokenStrings.Namespace, name);
            return true;
        }
        else if (Lexer.isTypenameName(name)) {
            this.recordLexTokenWData(this.m_cpos + name.length, TokenStrings.Type, name);
            return true;
        }
        else if (Lexer.isTemplateName(name)) {
            this.recordLexTokenWData(this.m_cpos + name.length, TokenStrings.Template, name);
            return true;
        }
        else if (Lexer.isIdentifierName(name)) {
            this.recordLexTokenWData(this.m_cpos + name.length, TokenStrings.Identifier, name);
            return true;
        }
        else {
            this.recordLexToken(this.m_cpos + name.length, TokenStrings.Error);
            return false;
        }
    }
    static isAttributeKW(str) {
        return AttributeStrings.indexOf(str) !== -1;
    }
    lex() {
        if (this.m_tokens.length !== 0) {
            return this.m_tokens;
        }
        this.m_tokens = [];
        while (this.m_cpos < this.m_input.length) {
            if (this.tryLexWS() || this.tryLexComment()) {
                //continue
            }
            else if (this.tryLexNumber() || this.tryLexString() || this.tryLexSymbol() || this.tryLexName()) {
                //continue
            }
            else {
                this.recordLexToken(this.m_cpos + 1, TokenStrings.Error);
            }
        }
        this.recordLexToken(this.m_input.length, TokenStrings.EndOfStream);
        return this.m_tokens;
    }
}
Lexer._s_whitespaceRe = /\s+/y;
Lexer._s_commentRe = /\/(?:\/[^\n\r]*|\*(?<multiline>[^\*]*\**)+?(?<multilineEndChar>\/|$))/y;
Lexer._s_numberRe = /[0-9]+/y;
Lexer._s_stringRe = /"[^"]*"/y;
Lexer._s_typedStringRe = /'[^']*'/y;
Lexer._s_symbolRe = /\W+/y;
Lexer._s_nameRe = /(\w+)|(recursive\?)/y;
class ParseError extends Error {
    constructor(line, message) {
        super(`Parse failure on line ${line} -- ${message}`);
        Object.setPrototypeOf(this, new.target.prototype);
    }
}
exports.ParseError = ParseError;
class Parser {
    constructor(assembly) {
        this.m_tokens = [];
        this.m_cpos = 0;
        this.m_epos = 0;
        this.m_penv = new parser_env_1.ParserEnvironment(assembly);
        this.m_errors = [];
        this.m_recoverStack = [];
    }
    initialize(toks) {
        this.m_tokens = toks;
        this.m_cpos = 0;
        this.m_epos = toks.length;
    }
    ////
    //Helpers
    static attributeSetContains(attr, attribs) {
        return attribs.indexOf(attr) !== -1;
    }
    getCurrentLine() {
        return this.m_tokens[this.m_cpos].line;
    }
    getCurrentSrcInfo() {
        const tk = this.m_tokens[this.m_cpos];
        return new SourceInfo(tk.line, 0, tk.pos, tk.span);
    }
    setRecover(pos) {
        this.m_recoverStack.push(pos);
    }
    clearRecover(pos) {
        this.m_recoverStack.pop();
    }
    processRecover() {
        this.m_cpos = this.m_recoverStack.pop();
    }
    raiseError(line, msg) {
        this.m_errors.push([line, msg]);
        throw new ParseError(line, msg);
    }
    scanMatchingParens(lp, rp) {
        let pscount = 1;
        for (let pos = this.m_cpos + 1; pos < this.m_epos; ++pos) {
            const tok = this.m_tokens[pos];
            if (tok.kind === lp) {
                pscount++;
            }
            else if (tok.kind === rp) {
                pscount--;
            }
            else {
                //nop
            }
            if (pscount === 0) {
                return pos + 1;
            }
        }
        return this.m_epos;
    }
    scanCodeParens() {
        let pscount = 1;
        for (let pos = this.m_cpos + 1; pos < this.m_epos; ++pos) {
            const tok = this.m_tokens[pos];
            if (LeftScanParens.indexOf(tok.kind) !== -1) {
                pscount++;
            }
            else if (RightScanParens.indexOf(tok.kind) !== -1) {
                pscount--;
            }
            else {
                //nop
            }
            if (pscount === 0) {
                return pos + 1;
            }
        }
        return this.m_epos;
    }
    setNamespaceAndFile(ns, file) {
        this.m_penv.setNamespaceAndFile(ns, file);
    }
    peekToken(pos) {
        return this.m_tokens[this.m_cpos + (pos || 0)].kind;
    }
    peekTokenData(pos) {
        return this.m_tokens[this.m_cpos + (pos || 0)].data;
    }
    testToken(kind) {
        return (this.m_cpos !== this.m_epos) && this.m_tokens[this.m_cpos].kind === kind;
    }
    testFollows(...kinds) {
        for (let i = 0; i < kinds.length; ++i) {
            if (this.m_cpos + i === this.m_epos || this.m_tokens[this.m_cpos + i].kind !== kinds[i]) {
                return false;
            }
        }
        return true;
    }
    testFollowsFrom(pos, ...kinds) {
        for (let i = 0; i < kinds.length; ++i) {
            if (pos + i === this.m_epos || this.m_tokens[pos + i].kind !== kinds[i]) {
                return false;
            }
        }
        return true;
    }
    consumeToken() {
        this.m_cpos++;
    }
    consumeTokenIf(kind) {
        if (this.testToken(kind)) {
            this.consumeToken();
        }
    }
    testAndConsumeTokenIf(kind) {
        const test = this.testToken(kind);
        if (test) {
            this.consumeToken();
        }
        return test;
    }
    consumeTokenAndGetValue() {
        const td = this.m_tokens[this.m_cpos].data;
        this.consumeToken();
        return td;
    }
    ensureToken(kind) {
        if (!this.testToken(kind)) {
            const found = this.m_tokens[this.m_cpos].data || this.m_tokens[this.m_cpos].kind;
            this.raiseError(this.m_tokens[this.m_cpos].line, `Expected "${kind}" but found "${found}"`);
        }
    }
    ensureAndConsumeToken(kind) {
        this.ensureToken(kind);
        this.consumeToken();
    }
    ensureNotToken(kind) {
        if (this.testToken(kind)) {
            this.raiseError(this.m_tokens[this.m_cpos].line, `Token "${kind}" is not allowed`);
        }
    }
    scanToken(tok) {
        let pos = this.m_cpos;
        while (pos !== this.m_epos) {
            if (this.m_tokens[pos].kind === tok) {
                return pos;
            }
            pos++;
        }
        return this.m_epos;
    }
    scanTokenOptions(...toks) {
        let pos = this.m_cpos;
        while (pos !== this.m_epos) {
            if (toks.indexOf(this.m_tokens[pos].kind) !== -1) {
                return pos;
            }
            pos++;
        }
        return this.m_epos;
    }
    parseListOf(start, end, sep, fn, specialToken) {
        let specialFound = false;
        let result = [];
        this.ensureAndConsumeToken(start);
        while (!this.testAndConsumeTokenIf(end)) {
            if (specialToken !== undefined && this.testAndConsumeTokenIf(specialToken)) {
                specialFound = true;
                this.ensureToken(end);
            }
            else {
                result.push(fn());
            }
            if (this.testAndConsumeTokenIf(sep)) {
                this.ensureNotToken(end);
            }
            else {
                this.ensureToken(end);
            }
        }
        return [result, specialFound];
    }
    ////
    //Misc parsing
    parseInvokableCommon(ispcode, isMember, noBody, attributes, isrecursive, pragmas, terms, termRestrictions, optSelfType) {
        const sinfo = this.getCurrentSrcInfo();
        const srcFile = this.m_penv.getCurrentFile();
        const line = this.getCurrentLine();
        let fparams = [];
        if (isMember) {
            fparams.push(new type_signature_1.FunctionParameter("this", optSelfType, false, false));
        }
        let restName = undefined;
        let restType = undefined;
        let resultType = this.m_penv.SpecialAutoSignature;
        const params = this.parseListOf("(", ")", ",", () => {
            const isrest = this.testAndConsumeTokenIf("...");
            const isref = this.testAndConsumeTokenIf("ref");
            if (isref && (isrest || ispcode)) {
                this.raiseError(line, "Cannot use ref parameters here");
            }
            this.ensureToken(TokenStrings.Identifier);
            const pname = this.consumeTokenAndGetValue();
            const isopt = this.testAndConsumeTokenIf("?");
            let argtype = this.m_penv.SpecialAutoSignature;
            if (this.testAndConsumeTokenIf(":")) {
                argtype = this.parseTypeSignature();
            }
            else {
                if (!ispcode) {
                    this.raiseError(line, "Auto typing is not supported for this");
                }
            }
            return [pname, argtype, isopt, isrest, isref];
        })[0];
        for (let i = 0; i < params.length; i++) {
            if (!params[i][3]) {
                fparams.push(new type_signature_1.FunctionParameter(params[i][0], params[i][1], params[i][2], params[i][4]));
            }
            else {
                if (i + 1 !== params.length) {
                    this.raiseError(line, "Rest parameter must be last in parameter list");
                }
                restName = params[i][0];
                restType = params[i][1];
            }
        }
        if (restName !== undefined && params.some((p) => p[2])) {
            this.raiseError(line, "Cannot have optional and rest parameters in a function");
        }
        if (this.testAndConsumeTokenIf(":")) {
            resultType = this.parseTypeSignature();
        }
        else {
            if (!ispcode) {
                this.raiseError(line, "Auto typing is not supported for this");
            }
        }
        const argNames = new Set([...(restName ? [restName] : []), ...fparams.map((param) => param.name)]);
        let preconds = [];
        let postconds = [];
        let body = undefined;
        let captured = new Set();
        if (noBody) {
            this.ensureAndConsumeToken(";");
        }
        else {
            if (ispcode) {
                this.ensureAndConsumeToken("=>");
            }
            else {
                [preconds, postconds] = this.parsePreAndPostConditions(argNames);
            }
            const bodyid = `${srcFile}::${sinfo.pos}`;
            try {
                this.m_penv.pushFunctionScope(new parser_env_1.FunctionScope(argNames));
                body = this.parseBody(bodyid, srcFile, fparams.map((p) => p.name));
                captured = this.m_penv.getCurrentFunctionScope().getCaptureVars();
                this.m_penv.popFunctionScope();
            }
            catch (ex) {
                this.m_penv.popFunctionScope();
                throw ex;
            }
        }
        if (ispcode) {
            return assembly_1.InvokeDecl.createPCodeInvokeDecl(sinfo, srcFile, attributes, isrecursive, fparams, restName, restType, resultType, captured, body);
        }
        else if (isMember) {
            return assembly_1.InvokeDecl.createMemberInvokeDecl(sinfo, srcFile, attributes, isrecursive, pragmas, terms, termRestrictions, fparams, restName, restType, resultType, preconds, postconds, body);
        }
        else {
            return assembly_1.InvokeDecl.createStaticInvokeDecl(sinfo, srcFile, attributes, isrecursive, pragmas, terms, termRestrictions, fparams, restName, restType, resultType, preconds, postconds, body);
        }
    }
    ////
    //Type parsing
    parseTypeSignature() {
        return this.parseOrCombinatorType();
    }
    parseOrCombinatorType() {
        const ltype = this.parsePostfixTypeReference();
        if (!this.testToken("|")) {
            return ltype;
        }
        else {
            this.consumeToken();
            return Parser.orOfTypeSignatures(ltype, this.parseOrCombinatorType());
        }
    }
    parsePostfixTypeReference() {
        let roottype = this.parseAndCombinatorType();
        while (this.testToken("?")) {
            roottype = this.parseNoneableType(roottype);
        }
        return roottype;
    }
    parseNoneableType(basetype) {
        this.ensureAndConsumeToken("?");
        return Parser.orOfTypeSignatures(basetype, this.m_penv.SpecialNoneSignature);
    }
    parseAndCombinatorType() {
        const line = this.getCurrentLine();
        const ltype = this.parseBaseTypeReference();
        if (!this.testToken("&")) {
            return ltype;
        }
        else {
            this.consumeToken();
            const rtype = this.parseAndCombinatorType();
            if (!(ltype instanceof type_signature_1.NominalTypeSignature || ltype instanceof type_signature_1.TemplateTypeSignature)) {
                this.raiseError(line, "Only nominal types can be used in a joined type");
            }
            if (!(rtype instanceof type_signature_1.NominalTypeSignature || rtype instanceof type_signature_1.TemplateTypeSignature)) {
                this.raiseError(line, "Only nominal types can be used in a joined type");
            }
            return Parser.andOfTypeSignatures(ltype, rtype);
        }
    }
    parseBaseTypeReference() {
        switch (this.peekToken()) {
            case TokenStrings.Template:
                return this.parseTemplateTypeReference();
            case TokenStrings.Namespace:
            case TokenStrings.Type:
                return this.parseNominalType();
            case "[":
                return this.parseTupleType();
            case "{":
                return this.parseRecordType();
            case "fn":
            case "recursive?":
            case "recursive":
                return this.parsePCodeType();
            default:
                {
                    this.ensureAndConsumeToken("(");
                    const ptype = this.parseTypeSignature();
                    this.ensureAndConsumeToken(")");
                    return ptype;
                }
        }
    }
    parseTemplateTypeReference() {
        return new type_signature_1.TemplateTypeSignature(this.consumeTokenAndGetValue());
    }
    parseNominalType() {
        const line = this.getCurrentLine();
        let ns = undefined;
        if (this.testToken(TokenStrings.Namespace)) {
            ns = this.consumeTokenAndGetValue();
            this.ensureAndConsumeToken("::");
        }
        const tname = this.consumeTokenAndGetValue();
        ns = this.m_penv.tryResolveNamespace(ns, tname);
        if (ns === undefined) {
            this.raiseError(line, "Could not resolve namespace");
        }
        if (!this.testToken("<")) {
            return new type_signature_1.NominalTypeSignature(ns, tname);
        }
        else {
            let terms = [];
            try {
                this.setRecover(this.scanMatchingParens("<", ">"));
                terms = this.parseListOf("<", ">", ",", () => {
                    return this.parseTypeSignature();
                })[0];
                this.clearRecover();
                return new type_signature_1.NominalTypeSignature(ns, tname, terms);
            }
            catch (ex) {
                this.processRecover();
                return new type_signature_1.ParseErrorTypeSignature();
            }
        }
    }
    parseTupleType() {
        const line = this.getCurrentLine();
        let entries = [];
        try {
            this.setRecover(this.scanMatchingParens("[", "]"));
            entries = this.parseListOf("[", "]", ",", () => {
                const isopt = this.testAndConsumeTokenIf("?");
                if (isopt) {
                    this.ensureAndConsumeToken(":");
                }
                const rtype = this.parseTypeSignature();
                return [rtype, isopt];
            })[0];
            const firstOpt = entries.findIndex((entry) => entry[1]);
            if (entries.slice(firstOpt).findIndex((entry) => !entry[0]) !== -1) {
                this.raiseError(line, "Optional entries must all come at end of tuple");
            }
            this.clearRecover();
            return new type_signature_1.TupleTypeSignature(entries);
        }
        catch (ex) {
            this.processRecover();
            return new type_signature_1.ParseErrorTypeSignature();
        }
    }
    parseRecordType() {
        let entries = [];
        try {
            this.setRecover(this.scanMatchingParens("{", "}"));
            entries = this.parseListOf("{", "}", ",", () => {
                this.ensureToken(TokenStrings.Identifier);
                const name = this.consumeTokenAndGetValue();
                const isopt = this.testAndConsumeTokenIf("?");
                this.ensureAndConsumeToken(":");
                const rtype = this.parseTypeSignature();
                return [name, rtype, isopt];
            })[0];
            this.clearRecover();
            return new type_signature_1.RecordTypeSignature(entries);
        }
        catch (ex) {
            this.processRecover();
            return new type_signature_1.ParseErrorTypeSignature();
        }
    }
    parsePCodeType() {
        let recursive = "no";
        if (this.testAndConsumeTokenIf("recursive?")) {
            recursive = "cond";
        }
        if (this.testAndConsumeTokenIf("recursive")) {
            recursive = "yes";
        }
        this.ensureAndConsumeToken("fn");
        try {
            this.setRecover(this.scanMatchingParens("(", ")"));
            let fparams = [];
            let restName = undefined;
            let restType = undefined;
            const params = this.parseListOf("(", ")", ",", () => {
                const isrest = this.testAndConsumeTokenIf("...");
                this.ensureToken(TokenStrings.Identifier);
                const pname = this.consumeTokenAndGetValue();
                const isopt = this.testAndConsumeTokenIf("?");
                this.ensureAndConsumeToken(":");
                const argtype = this.parseTypeSignature();
                return [pname, argtype, isopt, isrest];
            })[0];
            for (let i = 0; i < params.length; i++) {
                if (!params[i][3]) {
                    fparams.push(new type_signature_1.FunctionParameter(params[i][0], params[i][1], params[i][2], false));
                }
                else {
                    if (i + 1 !== params.length) {
                        this.raiseError(this.getCurrentLine(), "Rest parameter must be last in parameter list");
                    }
                    restName = params[i][0];
                    restType = params[i][1];
                }
            }
            if (restName !== undefined && params.some((p) => p[2])) {
                this.raiseError(this.getCurrentLine(), "Cannot have optional and rest parameters in a function type");
            }
            this.ensureAndConsumeToken("->");
            const resultType = this.parseTypeSignature();
            this.clearRecover();
            return new type_signature_1.FunctionTypeSignature(recursive, fparams, restName, restType, resultType);
        }
        catch (ex) {
            this.processRecover();
            return new type_signature_1.ParseErrorTypeSignature();
        }
    }
    static orOfTypeSignatures(t1, t2) {
        const types = [
            ...((t1 instanceof type_signature_1.UnionTypeSignature) ? t1.types : [t1]),
            ...((t2 instanceof type_signature_1.UnionTypeSignature) ? t2.types : [t2]),
        ];
        return new type_signature_1.UnionTypeSignature(types);
    }
    static andOfTypeSignatures(t1, t2) {
        const types = [
            ...((t1 instanceof type_signature_1.IntersectionTypeSignature) ? t1.types : [t1]),
            ...((t2 instanceof type_signature_1.IntersectionTypeSignature) ? t2.types : [t2]),
        ];
        return new type_signature_1.IntersectionTypeSignature(types);
    }
    ////
    //Expression parsing
    parseArguments(lparen, rparen) {
        const argSrcInfo = this.getCurrentSrcInfo();
        let seenNames = new Set();
        let args = [];
        try {
            this.setRecover(this.scanMatchingParens(lparen, rparen));
            this.ensureAndConsumeToken(lparen);
            while (!this.testAndConsumeTokenIf(rparen)) {
                const line = this.getCurrentLine();
                const isref = this.testAndConsumeTokenIf("ref");
                if (this.testFollows(TokenStrings.Identifier, "=")) {
                    const name = this.consumeTokenAndGetValue();
                    this.ensureAndConsumeToken("=");
                    const exp = this.parseExpression();
                    if (seenNames.has(name)) {
                        this.raiseError(line, "Cannot have duplicate named argument name");
                    }
                    if (name !== "_") {
                        seenNames.add(name);
                    }
                    args.push(new body_1.NamedArgument(isref, name, exp));
                }
                else {
                    const isSpread = this.testAndConsumeTokenIf("...");
                    const exp = this.parseExpression();
                    args.push(new body_1.PositionalArgument(isref, isSpread, exp));
                }
                if (this.testAndConsumeTokenIf(",")) {
                    this.ensureNotToken(rparen);
                }
                else {
                    this.ensureToken(rparen);
                }
            }
            this.clearRecover();
            return new body_1.Arguments(args);
        }
        catch (ex) {
            this.processRecover();
            return new body_1.Arguments([new body_1.PositionalArgument(false, false, new body_1.InvalidExpression(argSrcInfo))]);
        }
    }
    parseTemplateArguments() {
        try {
            this.setRecover(this.scanMatchingParens("<", ">"));
            let targs = [];
            this.ensureAndConsumeToken("<");
            while (!this.testAndConsumeTokenIf(">")) {
                targs.push(this.parseTypeSignature());
                if (this.testAndConsumeTokenIf(",")) {
                    this.ensureNotToken(">");
                }
                else {
                    this.ensureToken(">");
                }
            }
            this.clearRecover();
            return new body_1.TemplateArguments(targs);
        }
        catch (ex) {
            this.processRecover();
            return new body_1.TemplateArguments([]);
        }
    }
    parsePragmaArguments() {
        try {
            this.setRecover(this.scanMatchingParens("[", "]"));
            let pargs = [];
            let recursive = "no";
            this.ensureAndConsumeToken("[");
            while (!this.testAndConsumeTokenIf("]")) {
                if (this.testToken("recursive") || this.testToken("recursive?")) {
                    if (recursive !== "no") {
                        this.raiseError(this.getCurrentLine(), "Multiple recursive pragmas on call");
                    }
                    recursive = this.testToken("recursive") ? "yes" : "cond";
                    this.consumeToken();
                }
                else {
                    const ptype = this.parseTypeSignature();
                    this.ensureToken(TokenStrings.TypedString);
                    const pstr = this.consumeTokenAndGetValue();
                    pargs.push([ptype, pstr]);
                }
                if (this.testAndConsumeTokenIf(",")) {
                    this.ensureNotToken("]");
                }
                else {
                    this.ensureToken("]");
                }
            }
            this.clearRecover();
            return new body_1.PragmaArguments(recursive, pargs);
        }
        catch (ex) {
            this.processRecover();
            return new body_1.PragmaArguments("no", []);
        }
    }
    parseConstructorPrimary(otype) {
        const sinfo = this.getCurrentSrcInfo();
        const args = this.parseArguments("{", "}");
        return new body_1.ConstructorPrimaryExpression(sinfo, otype, args);
    }
    parseConstructorPrimaryWithFactory(otype) {
        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken("@");
        this.ensureToken(TokenStrings.Identifier);
        const fname = this.consumeTokenAndGetValue();
        const targs = this.testToken("<") ? this.parseTemplateArguments() : new body_1.TemplateArguments([]);
        const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new body_1.PragmaArguments("no", []);
        const args = this.parseArguments("(", ")");
        return new body_1.ConstructorPrimaryWithFactoryExpression(sinfo, otype, fname, pragmas, targs, args);
    }
    parsePCodeTerm() {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();
        const isrecursive = this.testAndConsumeTokenIf("recursive");
        this.ensureAndConsumeToken("fn");
        const sig = this.parseInvokableCommon(true, false, false, [], isrecursive ? "yes" : "no", [], [], []);
        const someAuto = sig.params.some((param) => param.type instanceof type_signature_1.AutoTypeSignature) || (sig.optRestType !== undefined && sig.optRestType instanceof type_signature_1.AutoTypeSignature) || sig.resultType instanceof type_signature_1.AutoTypeSignature;
        const allAuto = sig.params.every((param) => param.type instanceof type_signature_1.AutoTypeSignature) && (sig.optRestType === undefined || sig.optRestType instanceof type_signature_1.AutoTypeSignature) && sig.resultType instanceof type_signature_1.AutoTypeSignature;
        if (someAuto && !allAuto) {
            this.raiseError(line, "Cannot have mixed of auto propagated and explicit types on lambda arguments/return");
        }
        sig.captureSet.forEach((v) => {
            this.m_penv.getCurrentFunctionScope().useLocalVar(v);
        });
        return new body_1.ConstructorPCodeExpression(sinfo, allAuto, sig);
    }
    parsePrimaryExpression() {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();
        const tk = this.peekToken();
        if (tk === "none") {
            this.consumeToken();
            return new body_1.LiteralNoneExpression(sinfo);
        }
        else if (tk === "true" || tk === "false") {
            this.consumeToken();
            return new body_1.LiteralBoolExpression(sinfo, tk === "true");
        }
        else if (tk === TokenStrings.Int) {
            const istr = this.consumeTokenAndGetValue();
            return new body_1.LiteralIntegerExpression(sinfo, istr);
        }
        else if (tk === TokenStrings.String) {
            const sstr = this.consumeTokenAndGetValue(); //keep in escaped format
            return new body_1.LiteralStringExpression(sinfo, sstr);
        }
        else if (tk === TokenStrings.Identifier) {
            const istr = this.consumeTokenAndGetValue();
            const ns = this.m_penv.tryResolveNamespace(undefined, istr);
            if (ns === undefined) {
                //Ignore special postcondition _return_ variable but everything else should be processed
                if (istr !== "_return_") {
                    this.m_penv.getCurrentFunctionScope().useLocalVar(istr);
                }
                if (this.testToken("[")) {
                    const pragmas = this.parsePragmaArguments();
                    const args = this.parseArguments("(", ")");
                    return new body_1.PCodeInvokeExpression(sinfo, istr, pragmas, args);
                }
                else if (this.testToken("(")) {
                    const args = this.parseArguments("(", ")");
                    return new body_1.PCodeInvokeExpression(sinfo, istr, new body_1.PragmaArguments("no", []), args);
                }
                else {
                    return new body_1.AccessVariableExpression(sinfo, istr);
                }
            }
            else {
                const targs = this.testToken("<") ? this.parseTemplateArguments() : new body_1.TemplateArguments([]);
                const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new body_1.PragmaArguments("no", []);
                const args = this.parseArguments("(", ")");
                return new body_1.CallNamespaceFunctionExpression(sinfo, ns, istr, targs, pragmas, args);
            }
        }
        else if (tk === "fn" || this.testFollows("recursive", "fn")) {
            return this.parsePCodeTerm();
        }
        else if (tk === "(") {
            try {
                this.setRecover(this.scanMatchingParens("(", ")"));
                this.consumeToken();
                const exp = this.parseExpression();
                this.ensureAndConsumeToken(")");
                this.clearRecover();
                return exp;
            }
            catch (ex) {
                this.processRecover();
                return new body_1.InvalidExpression(sinfo);
            }
        }
        else if (this.testToken("[")) {
            const args = this.parseArguments("[", "]");
            return new body_1.ConstructorTupleExpression(sinfo, args);
        }
        else if (this.testToken("{")) {
            const args = this.parseArguments("{", "}");
            return new body_1.ConstructorRecordExpression(sinfo, args);
        }
        else if (this.testFollows(TokenStrings.Namespace, "::", TokenStrings.Identifier)) {
            //it is a namespace access of some type
            const ns = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();
            if (!this.testToken("<") && !this.testToken("[") && !this.testToken("(")) {
                //just a constant access
                return new body_1.AccessNamespaceConstantExpression(sinfo, ns, name);
            }
            else {
                const targs = this.testToken("<") ? this.parseTemplateArguments() : new body_1.TemplateArguments([]);
                const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new body_1.PragmaArguments("no", []);
                const args = this.parseArguments("(", ")");
                return new body_1.CallNamespaceFunctionExpression(sinfo, ns, name, targs, pragmas, args);
            }
        }
        else {
            //we should find a type (nominal here) and it is either (1) a constructor (2) constructor with factory or (3) static invoke
            const ttype = this.parseTypeSignature();
            if (this.testFollows("::", TokenStrings.Identifier)) {
                this.consumeToken();
                const name = this.consumeTokenAndGetValue();
                if (!this.testToken("<") && !this.testToken("[") && !this.testToken("(")) {
                    //just a static access
                    return new body_1.AccessStaticFieldExpression(sinfo, ttype, name);
                }
                else {
                    const targs = this.testToken("<") ? this.parseTemplateArguments() : new body_1.TemplateArguments([]);
                    const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new body_1.PragmaArguments("no", []);
                    const args = this.parseArguments("(", ")");
                    return new body_1.CallStaticFunctionExpression(sinfo, ttype, name, targs, pragmas, args);
                }
            }
            else if (this.testToken(TokenStrings.TypedString) || this.testFollows("@", TokenStrings.TypedString)) {
                if (this.testAndConsumeTokenIf("@")) {
                    const sstr = this.consumeTokenAndGetValue(); //keep in escaped format
                    return new body_1.LiteralTypedStringConstructorExpression(sinfo, sstr, ttype);
                }
                else {
                    const sstr = this.consumeTokenAndGetValue(); //keep in escaped format
                    return new body_1.LiteralTypedStringExpression(sinfo, sstr, ttype);
                }
            }
            else if (this.testFollows("@", TokenStrings.Identifier)) {
                return this.parseConstructorPrimaryWithFactory(ttype);
            }
            else if (this.testToken("{")) {
                return this.parseConstructorPrimary(ttype);
            }
            else {
                this.raiseError(line, "Unknown token sequence in parsing expression");
                return new body_1.InvalidExpression(sinfo);
            }
        }
    }
    handleSpecialCaseMethods(sinfo, isElvis, specificResolve, name) {
        if (specificResolve !== undefined) {
            this.raiseError(this.getCurrentLine(), "Cannot use specific resolve on special methods");
        }
        const line = this.getCurrentLine();
        if (name === "project") {
            this.ensureToken("<");
            const terms = this.parseTemplateArguments();
            if (terms.targs.length !== 1) {
                this.raiseError(line, "The project method expects a single template type argument");
            }
            const type = terms.targs[0];
            if (!(type instanceof type_signature_1.TemplateTypeSignature || type instanceof type_signature_1.NominalTypeSignature || type instanceof type_signature_1.RecordTypeSignature || type instanceof type_signature_1.TupleTypeSignature)) {
                this.raiseError(line, "Can only project over record, tuple, or concept contraints");
            }
            this.ensureAndConsumeToken("(");
            this.ensureAndConsumeToken(")");
            return new body_1.PostfixProjectFromType(sinfo, isElvis, type);
        }
        else if (name === "update") {
            if (this.testFollows("(", TokenStrings.Int)) {
                const updates = this.parseListOf("(", ")", ",", () => {
                    this.ensureToken(TokenStrings.Int);
                    const idx = Number.parseInt(this.consumeTokenAndGetValue());
                    this.ensureAndConsumeToken("=");
                    const value = this.parseExpression();
                    return [idx, value];
                })[0].sort((a, b) => a[0] - b[0]);
                return new body_1.PostfixModifyWithIndecies(sinfo, isElvis, updates);
            }
            else if (this.testFollows("(", TokenStrings.Identifier)) {
                const updates = this.parseListOf("(", ")", ",", () => {
                    this.ensureToken(TokenStrings.Identifier);
                    const uname = this.consumeTokenAndGetValue();
                    this.ensureAndConsumeToken("=");
                    const value = this.parseExpression();
                    return [uname, value];
                })[0].sort((a, b) => a[0].localeCompare(b[0]));
                return new body_1.PostfixModifyWithNames(sinfo, isElvis, updates);
            }
            else {
                this.raiseError(line, "Expected list of property/field or tuple updates");
                return undefined;
            }
        }
        else if (name === "merge") {
            this.ensureAndConsumeToken("(");
            const update = this.parseExpression();
            this.ensureAndConsumeToken(")");
            return new body_1.PostfixStructuredExtend(sinfo, isElvis, update);
        }
        else {
            this.raiseError(line, "'difference' operation not implemented yet");
            return undefined;
        }
    }
    parsePostfixExpression() {
        const rootinfo = this.getCurrentSrcInfo();
        let rootexp = this.parsePrimaryExpression();
        let ops = [];
        while (true) {
            const sinfo = this.getCurrentSrcInfo();
            const tk = this.peekToken();
            if (tk === "." || tk === "?.") {
                const isElvis = this.testToken("?.");
                this.consumeToken();
                if (this.testToken(TokenStrings.Int)) {
                    const index = Number.parseInt(this.consumeTokenAndGetValue());
                    ops.push(new body_1.PostfixAccessFromIndex(sinfo, isElvis, index));
                }
                else if (this.testToken("[")) {
                    const indecies = this.parseListOf("[", "]", ",", () => {
                        this.ensureToken(TokenStrings.Int);
                        return Number.parseInt(this.consumeTokenAndGetValue());
                    })[0];
                    ops.push(new body_1.PostfixProjectFromIndecies(sinfo, isElvis, indecies));
                }
                else if (this.testToken(TokenStrings.Identifier)) {
                    const name = this.consumeTokenAndGetValue();
                    ops.push(new body_1.PostfixAccessFromName(sinfo, isElvis, name));
                }
                else {
                    this.ensureToken("{");
                    const names = this.parseListOf("{", "}", ",", () => {
                        this.ensureToken(TokenStrings.Identifier);
                        return this.consumeTokenAndGetValue();
                    })[0].sort();
                    ops.push(new body_1.PostfixProjectFromNames(sinfo, isElvis, names));
                }
            }
            else if (tk === "->" || tk === "?->") {
                const isElvis = this.testToken("?->");
                this.consumeToken();
                let specificResolve = undefined;
                if (this.testToken(TokenStrings.Namespace) || this.testToken(TokenStrings.Type) || this.testToken(TokenStrings.Template)) {
                    specificResolve = this.parseTypeSignature();
                    this.ensureAndConsumeToken("::");
                }
                this.ensureToken(TokenStrings.Identifier);
                const name = this.consumeTokenAndGetValue();
                if (SpecialInvokeNames.includes(name)) {
                    ops.push(this.handleSpecialCaseMethods(sinfo, isElvis, specificResolve, name));
                }
                else {
                    const terms = this.testToken("<") ? this.parseTemplateArguments() : new body_1.TemplateArguments([]);
                    const pragmas = this.testToken("[") ? this.parsePragmaArguments() : new body_1.PragmaArguments("no", []);
                    const args = this.parseArguments("(", ")");
                    ops.push(new body_1.PostfixInvoke(sinfo, isElvis, specificResolve, name, terms, pragmas, args));
                }
            }
            else {
                if (ops.length === 0) {
                    return rootexp;
                }
                else {
                    return new body_1.PostfixOp(rootinfo, rootexp, ops);
                }
            }
        }
    }
    parseStatementExpression() {
        if (this.testToken("{|")) {
            return this.parseBlockStatementExpression();
        }
        else if (this.testToken("if")) {
            return this.parseIfExpression();
        }
        else if (this.testToken("switch")) {
            return this.parseMatchExpression();
        }
        else {
            return this.parsePostfixExpression();
        }
    }
    parsePrefixExpression() {
        const sinfo = this.getCurrentSrcInfo();
        if (this.testToken("+") || this.testToken("-") || this.testToken("!")) {
            const op = this.consumeTokenAndGetValue();
            return new body_1.PrefixOp(sinfo, op, this.parsePrefixExpression());
        }
        else {
            return this.parseStatementExpression();
        }
    }
    parseMultiplicativeExpression() {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parsePrefixExpression();
        if (this.testToken("*") || this.testToken("/") || this.testToken("%")) {
            const op = this.consumeTokenAndGetValue();
            return new body_1.BinOpExpression(sinfo, exp, op, this.parseMultiplicativeExpression());
        }
        else {
            return exp;
        }
    }
    parseAdditiveExpression() {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseMultiplicativeExpression();
        if (this.testToken("+") || this.testToken("-")) {
            const op = this.consumeTokenAndGetValue();
            return new body_1.BinOpExpression(sinfo, exp, op, this.parseAdditiveExpression());
        }
        else {
            return exp;
        }
    }
    parseRelationalExpression() {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseAdditiveExpression();
        if (this.testToken("==") || this.testToken("!=")) {
            const op = this.consumeTokenAndGetValue();
            return new body_1.BinEqExpression(sinfo, exp, op, this.parseRelationalExpression());
        }
        else if (this.testToken("<") || this.testToken(">") || this.testToken("<=") || this.testToken(">=")) {
            const op = this.consumeTokenAndGetValue();
            return new body_1.BinCmpExpression(sinfo, exp, op, this.parseRelationalExpression());
        }
        else {
            return exp;
        }
    }
    parseImpliesExpression() {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseRelationalExpression();
        if (this.testAndConsumeTokenIf("==>")) {
            return new body_1.BinLogicExpression(sinfo, exp, "==>", this.parseImpliesExpression());
        }
        else {
            return exp;
        }
    }
    parseAndExpression() {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseImpliesExpression();
        if (this.testAndConsumeTokenIf("&&")) {
            return new body_1.BinLogicExpression(sinfo, exp, "&&", this.parseAndExpression());
        }
        else {
            return exp;
        }
    }
    parseOrExpression() {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseAndExpression();
        if (this.testAndConsumeTokenIf("||")) {
            return new body_1.BinLogicExpression(sinfo, exp, "||", this.parseOrExpression());
        }
        else {
            return exp;
        }
    }
    parseNonecheckExpression() {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseOrExpression();
        if (this.testAndConsumeTokenIf("?&")) {
            return new body_1.NonecheckExpression(sinfo, exp, this.parseNonecheckExpression());
        }
        else {
            return exp;
        }
    }
    parseCoalesceExpression() {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseNonecheckExpression();
        if (this.testAndConsumeTokenIf("?|")) {
            return new body_1.CoalesceExpression(sinfo, exp, this.parseCoalesceExpression());
        }
        else {
            return exp;
        }
    }
    parseSelectExpression() {
        const sinfo = this.getCurrentSrcInfo();
        const texp = this.parseCoalesceExpression();
        if (this.testAndConsumeTokenIf("?")) {
            const exp1 = this.parseCoalesceExpression();
            this.ensureAndConsumeToken(":");
            const exp2 = this.parseSelectExpression();
            return new body_1.SelectExpression(sinfo, texp, exp1, exp2);
        }
        else {
            return texp;
        }
    }
    parseExpOrExpression() {
        const sinfo = this.getCurrentSrcInfo();
        const texp = this.parseSelectExpression();
        if (this.testAndConsumeTokenIf("or")) {
            if (!this.testToken("return") && !this.testToken("yield")) {
                this.raiseError(this.getCurrentLine(), "Expected 'return' or 'yield");
            }
            const action = this.consumeTokenAndGetValue();
            let value = undefined;
            let cond = undefined;
            if (!this.testToken(";")) {
                if (this.testToken("when")) {
                    this.consumeToken();
                    cond = this.parseExpression();
                }
                else {
                    value = this.parseExpression();
                    if (this.testToken("when")) {
                        this.consumeToken();
                        cond = this.parseExpression();
                    }
                }
            }
            return new body_1.ExpOrExpression(sinfo, texp, action, value, cond);
        }
        else {
            return texp;
        }
    }
    parseBlockStatementExpression() {
        const sinfo = this.getCurrentSrcInfo();
        this.m_penv.getCurrentFunctionScope().pushLocalScope();
        let stmts = [];
        try {
            this.setRecover(this.scanMatchingParens("{|", "|}"));
            this.consumeToken();
            while (!this.testAndConsumeTokenIf("|}")) {
                stmts.push(this.parseStatement());
            }
            this.m_penv.getCurrentFunctionScope().popLocalScope();
            this.clearRecover();
            return new body_1.BlockStatementExpression(sinfo, stmts);
        }
        catch (ex) {
            this.m_penv.getCurrentFunctionScope().popLocalScope();
            this.processRecover();
            return new body_1.BlockStatementExpression(sinfo, [new body_1.InvalidStatement(sinfo)]);
        }
    }
    parseIfExpression() {
        const sinfo = this.getCurrentSrcInfo();
        let conds = [];
        this.ensureAndConsumeToken("if");
        this.ensureAndConsumeToken("(");
        const iftest = this.parseExpression();
        this.ensureAndConsumeToken(")");
        const ifbody = this.parseExpression();
        conds.push(new body_1.CondBranchEntry(iftest, ifbody));
        while (this.testAndConsumeTokenIf("elif")) {
            this.ensureAndConsumeToken("(");
            const eliftest = this.parseExpression();
            this.ensureAndConsumeToken(")");
            const elifbody = this.parseExpression();
            conds.push(new body_1.CondBranchEntry(eliftest, elifbody));
        }
        this.ensureAndConsumeToken("else");
        const elsebody = this.parseExpression();
        return new body_1.IfExpression(sinfo, new body_1.IfElse(conds, elsebody));
    }
    parseMatchExpression() {
        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken("switch");
        this.ensureAndConsumeToken("(");
        const mexp = this.parseExpression();
        this.ensureAndConsumeToken(")");
        let entries = [];
        this.ensureAndConsumeToken("{");
        while (this.testToken("type") || this.testToken("case")) {
            if (this.testToken("type")) {
                entries.push(this.parseMatchEntry(sinfo, true, () => this.parseExpression()));
            }
            else {
                entries.push(this.parseMatchEntry(sinfo, false, () => this.parseExpression()));
            }
        }
        this.ensureAndConsumeToken("}");
        return new body_1.MatchExpression(sinfo, mexp, entries);
    }
    parseExpression() {
        return this.parseExpOrExpression();
    }
    ////
    //Statement parsing
    parseStructuredAssignment(sinfo, vars, trequired, decls) {
        if (this.testToken("[")) {
            const assigns = this.parseListOf("[", "]", ",", () => {
                return this.parseStructuredAssignment(this.getCurrentSrcInfo(), vars, trequired, decls);
            })[0];
            return new body_1.TupleStructuredAssignment(assigns);
        }
        else if (this.testToken("{")) {
            const assigns = this.parseListOf("{", "}", ",", () => {
                this.ensureToken(TokenStrings.Identifier);
                const name = this.consumeTokenAndGetValue();
                this.ensureAndConsumeToken("=");
                const subg = this.parseStructuredAssignment(this.getCurrentSrcInfo(), vars, trequired, decls);
                return [name, subg];
            })[0];
            return new body_1.RecordStructuredAssignment(assigns);
        }
        else {
            if (this.testToken("var")) {
                if (vars !== undefined) {
                    this.raiseError(sinfo.line, "Cannot mix var decl before and inside structured assign");
                }
                this.consumeToken();
                const isConst = !this.testAndConsumeTokenIf("!");
                this.ensureToken(TokenStrings.Identifier);
                const name = this.consumeTokenAndGetValue();
                if (decls.has(name)) {
                    this.raiseError(sinfo.line, "Variable is already defined in scope");
                }
                decls.add(name);
                const isopt = this.testAndConsumeTokenIf("?");
                let itype = this.m_penv.SpecialAutoSignature;
                if (trequired) {
                    this.ensureAndConsumeToken(":");
                    itype = this.parseTypeSignature();
                }
                else {
                    if (this.testAndConsumeTokenIf(":")) {
                        itype = this.parseTypeSignature();
                    }
                }
                return new body_1.VariableDeclarationStructuredAssignment(isopt, name, isConst, itype);
            }
            else if (this.testToken(TokenStrings.Identifier)) {
                const name = this.consumeTokenAndGetValue();
                if (name === "_") {
                    const isopt = this.testAndConsumeTokenIf("?");
                    let itype = this.m_penv.SpecialAnySignature;
                    if (trequired) {
                        this.ensureAndConsumeToken(":");
                        itype = this.parseTypeSignature();
                    }
                    else {
                        if (this.testAndConsumeTokenIf(":")) {
                            itype = this.parseTypeSignature();
                        }
                    }
                    return new body_1.IgnoreTermStructuredAssignment(isopt, itype);
                }
                else {
                    const isopt = this.testAndConsumeTokenIf("?");
                    let itype = this.m_penv.SpecialAutoSignature;
                    if (trequired && vars !== undefined) {
                        this.ensureAndConsumeToken(":");
                        itype = this.parseTypeSignature();
                    }
                    else {
                        if (this.testAndConsumeTokenIf(":")) {
                            itype = this.parseTypeSignature();
                        }
                    }
                    if (vars !== undefined) {
                        if (decls.has(name)) {
                            this.raiseError(sinfo.line, "Variable is already defined in scope");
                        }
                        decls.add(name);
                        if (vars === "var") {
                            return new body_1.VariableDeclarationStructuredAssignment(isopt, name, true, itype);
                        }
                        else {
                            return new body_1.VariableDeclarationStructuredAssignment(isopt, name, false, itype);
                        }
                    }
                    else {
                        if (!this.m_penv.getCurrentFunctionScope().isVarNameDefined(name)) {
                            this.raiseError(sinfo.line, "Variable is not defined in scope");
                        }
                        return new body_1.VariableAssignmentStructuredAssignment(isopt, name);
                    }
                }
            }
            else {
                const cexp = this.parseExpression();
                return new body_1.ConstValueStructuredAssignment(cexp);
            }
        }
    }
    parseLineStatement() {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();
        const tk = this.peekToken();
        if (tk === ";") {
            this.consumeToken();
            return new body_1.EmptyStatement(sinfo);
        }
        else if (tk === "var") {
            this.consumeToken();
            const isConst = !this.testAndConsumeTokenIf("!");
            if (this.testToken("[") || this.testToken("{")) {
                let decls = new Set();
                const assign = this.parseStructuredAssignment(this.getCurrentSrcInfo(), isConst ? "var" : "var!", false, decls);
                decls.forEach((dv) => {
                    if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(dv)) {
                        this.raiseError(line, "Variable name is already defined");
                    }
                    this.m_penv.getCurrentFunctionScope().defineLocalVar(dv);
                });
                this.ensureAndConsumeToken("=");
                const exp = this.parseExpression();
                this.ensureAndConsumeToken(";");
                return new body_1.StructuredVariableAssignmentStatement(sinfo, assign, exp);
            }
            else {
                this.ensureToken(TokenStrings.Identifier);
                const name = this.consumeTokenAndGetValue();
                if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(name)) {
                    this.raiseError(line, "Variable is already defined in scope");
                }
                this.m_penv.getCurrentFunctionScope().defineLocalVar(name);
                const vtype = this.testAndConsumeTokenIf(":") ? this.parseTypeSignature() : this.m_penv.SpecialAutoSignature;
                const exp = this.testAndConsumeTokenIf("=") ? this.parseExpression() : undefined;
                if (exp === undefined && isConst) {
                    this.raiseError(line, "Const variable declaration must include an assignment to the variable");
                }
                this.ensureAndConsumeToken(";");
                return new body_1.VariableDeclarationStatement(sinfo, name, isConst, vtype, exp);
            }
        }
        else if (tk === "[" || tk === "{") {
            let decls = new Set();
            const assign = this.parseStructuredAssignment(this.getCurrentSrcInfo(), undefined, false, decls);
            decls.forEach((dv) => {
                if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(dv)) {
                    this.raiseError(line, "Variable name is already defined");
                }
                this.m_penv.getCurrentFunctionScope().defineLocalVar(dv);
            });
            this.ensureAndConsumeToken("=");
            const exp = this.parseExpression();
            this.ensureAndConsumeToken(";");
            return new body_1.StructuredVariableAssignmentStatement(sinfo, assign, exp);
        }
        else if (tk === TokenStrings.Identifier) {
            const name = this.consumeTokenAndGetValue();
            if (!this.m_penv.getCurrentFunctionScope().isVarNameDefined(name)) {
                this.raiseError(line, "Variable is not defined in scope");
            }
            this.ensureAndConsumeToken("=");
            const exp = this.parseExpression();
            this.ensureAndConsumeToken(";");
            return new body_1.VariableAssignmentStatement(sinfo, name, exp);
        }
        else if (tk === "return") {
            this.consumeToken();
            const exp = this.parseExpression();
            this.ensureAndConsumeToken(";");
            return new body_1.ReturnStatement(sinfo, exp);
        }
        else if (tk === "yield") {
            this.consumeToken();
            const exp = this.parseExpression();
            this.ensureAndConsumeToken(";");
            return new body_1.YieldStatement(sinfo, exp);
        }
        else if (tk === "abort") {
            this.consumeToken();
            this.ensureAndConsumeToken(";");
            return new body_1.AbortStatement(sinfo);
        }
        else if (tk === "assert") {
            this.consumeToken();
            const exp = this.parseExpression();
            this.ensureAndConsumeToken(";");
            return new body_1.AssertStatement(sinfo, exp);
        }
        else if (tk === "check") {
            this.consumeToken();
            const exp = this.parseExpression();
            this.ensureAndConsumeToken(";");
            return new body_1.CheckStatement(sinfo, exp);
        }
        else if (tk === "_debug") {
            this.consumeToken();
            let value = undefined;
            if (this.testToken("(")) {
                this.consumeToken();
                value = this.parseExpression();
                this.ensureAndConsumeToken(")");
            }
            this.ensureAndConsumeToken(";");
            return new body_1.DebugStatement(sinfo, value);
        }
        else {
            this.m_cpos = this.scanToken(";");
            return new body_1.InvalidStatement(sinfo);
        }
    }
    parseBlockStatement() {
        const sinfo = this.getCurrentSrcInfo();
        this.m_penv.getCurrentFunctionScope().pushLocalScope();
        let stmts = [];
        try {
            this.setRecover(this.scanMatchingParens("{", "}"));
            this.consumeToken();
            while (!this.testAndConsumeTokenIf("}")) {
                stmts.push(this.parseStatement());
            }
            this.m_penv.getCurrentFunctionScope().popLocalScope();
            if (stmts.length === 0) {
                this.raiseError(this.getCurrentLine(), "No empty blocks");
            }
            this.clearRecover();
            return new body_1.BlockStatement(sinfo, stmts);
        }
        catch (ex) {
            this.m_penv.getCurrentFunctionScope().popLocalScope();
            this.processRecover();
            return new body_1.BlockStatement(sinfo, [new body_1.InvalidStatement(sinfo)]);
        }
    }
    parseIfElseStatement() {
        const sinfo = this.getCurrentSrcInfo();
        let conds = [];
        this.ensureAndConsumeToken("if");
        this.ensureAndConsumeToken("(");
        const iftest = this.parseExpression();
        this.ensureAndConsumeToken(")");
        const ifbody = this.parseBlockStatement();
        conds.push(new body_1.CondBranchEntry(iftest, ifbody));
        while (this.testAndConsumeTokenIf("elif")) {
            this.ensureAndConsumeToken("(");
            const eliftest = this.parseExpression();
            this.ensureAndConsumeToken(")");
            const elifbody = this.parseBlockStatement();
            conds.push(new body_1.CondBranchEntry(eliftest, elifbody));
        }
        const elsebody = this.testAndConsumeTokenIf("else") ? this.parseBlockStatement() : undefined;
        return new body_1.IfElseStatement(sinfo, new body_1.IfElse(conds, elsebody));
    }
    parseMatchGuard(sinfo, istypematch) {
        if (this.testToken(TokenStrings.Identifier)) {
            const tv = this.consumeTokenAndGetValue();
            if (tv !== "_") {
                this.raiseError(sinfo.line, "Expected wildcard match");
            }
            return new body_1.WildcardMatchGuard();
        }
        let typecheck = undefined;
        let layoutcheck = undefined;
        let decls = new Set();
        if (istypematch) {
            typecheck = this.parseTypeSignature();
        }
        else {
            let varinfo = undefined;
            if (this.testAndConsumeTokenIf("var")) {
                varinfo = (this.testAndConsumeTokenIf("!") ? "var!" : "var");
            }
            layoutcheck = this.parseStructuredAssignment(sinfo, varinfo, true, decls);
        }
        let whencheck = undefined;
        if (this.testAndConsumeTokenIf("when")) {
            whencheck = this.parseExpression();
        }
        if (istypematch) {
            return new body_1.TypeMatchGuard(typecheck, whencheck);
        }
        else {
            return new body_1.StructureMatchGuard(layoutcheck, decls, whencheck);
        }
    }
    parseMatchEntry(sinfo, istypematch, actionp) {
        this.consumeToken();
        const guard = this.parseMatchGuard(sinfo, istypematch);
        this.ensureAndConsumeToken("=>");
        const action = actionp();
        return new body_1.MatchEntry(guard, action);
    }
    parseMatchStatement() {
        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken("switch");
        this.ensureAndConsumeToken("(");
        const mexp = this.parseExpression();
        this.ensureAndConsumeToken(")");
        let entries = [];
        this.ensureAndConsumeToken("{");
        while (this.testToken("type") || this.testToken("case")) {
            if (this.testToken("type")) {
                entries.push(this.parseMatchEntry(sinfo, true, () => this.parseBlockStatement()));
            }
            else {
                entries.push(this.parseMatchEntry(sinfo, false, () => this.parseBlockStatement()));
            }
        }
        this.ensureAndConsumeToken("}");
        return new body_1.MatchStatement(sinfo, mexp, entries);
    }
    parseStatement() {
        if (this.testToken("if")) {
            return this.parseIfElseStatement();
        }
        else if (this.testToken("switch")) {
            return this.parseMatchStatement();
        }
        else {
            return this.parseLineStatement();
        }
    }
    parseBody(bodyid, file, pnames) {
        if (this.testToken("#")) {
            this.consumeToken();
            this.ensureToken(TokenStrings.Identifier);
            return new body_1.BodyImplementation(bodyid, file, this.consumeTokenAndGetValue());
        }
        else if (this.testToken("{")) {
            if (this.testFollows("{", TokenStrings.Identifier, "=") && !pnames.includes(this.peekTokenData(1))) {
                //This is ambigious with the record constructor {p=exp ...} and the statement block {x=exp; ...}
                //However it is illegal to set a variable before declaration -- only option is updating a ref parameter so we check that
                return new body_1.BodyImplementation(bodyid, file, this.parseExpression());
            }
            else {
                return new body_1.BodyImplementation(bodyid, file, this.parseBlockStatement());
            }
        }
        else {
            return new body_1.BodyImplementation(bodyid, file, this.parseExpression());
        }
    }
    ////
    //Decl parsing
    parseAttributes() {
        let attributes = [];
        while (Lexer.isAttributeKW(this.peekToken())) {
            attributes.push(this.consumeTokenAndGetValue());
        }
        return attributes;
    }
    parseDeclPragmas() {
        let pragmas = [];
        while (this.testToken("pragma")) {
            const ts = this.parseTypeSignature();
            this.ensureToken(TokenStrings.TypedString);
            const sl = this.consumeTokenAndGetValue();
            pragmas.push([ts, sl]);
        }
        return pragmas;
    }
    parseTermDeclarations() {
        let terms = [];
        if (this.testToken("<")) {
            terms = this.parseListOf("<", ">", ",", () => {
                this.ensureToken(TokenStrings.Template);
                const templatename = this.consumeTokenAndGetValue();
                const tconstraint = this.testAndConsumeTokenIf("where") ? this.parseTypeSignature() : this.m_penv.SpecialAnySignature;
                return new assembly_1.TemplateTermDecl(templatename, tconstraint);
            })[0];
        }
        return terms;
    }
    parseTermRestrictions() {
        let terms = [];
        if (this.testFollows("{", "when")) {
            terms = this.parseListOf("{", "}", ",", () => {
                this.consumeTokenIf("when");
                this.ensureToken(TokenStrings.Template);
                const templatename = this.consumeTokenAndGetValue();
                const tconstraint = this.parseTypeSignature();
                return new assembly_1.TemplateTermRestriction(templatename, tconstraint);
            })[0];
        }
        return terms;
    }
    parsePreAndPostConditions(argnames) {
        let preconds = [];
        try {
            this.m_penv.pushFunctionScope(new parser_env_1.FunctionScope(new Set(argnames)));
            while (this.testToken("requires") || this.testToken("xrequires")) {
                if (this.testToken("requires")) {
                    this.consumeToken();
                    preconds.push([this.parseExpression(), false]);
                }
                else {
                    this.consumeToken();
                    preconds.push([this.parseExpression(), true]);
                }
                this.ensureAndConsumeToken(";");
            }
        }
        finally {
            this.m_penv.popFunctionScope();
        }
        let postconds = [];
        try {
            this.m_penv.pushFunctionScope(new parser_env_1.FunctionScope(new Set(argnames).add("_return_")));
            while (this.testAndConsumeTokenIf("ensures")) {
                postconds.push(this.parseExpression());
                this.ensureAndConsumeToken(";");
            }
        }
        finally {
            this.m_penv.popFunctionScope();
        }
        return [preconds, postconds];
    }
    parseNamespaceUsing(currentDecl) {
        //from NS using {...} ;
        this.ensureAndConsumeToken("from");
        this.ensureToken(TokenStrings.Namespace);
        const fromns = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken("using");
        const names = this.parseListOf("{", "}", ",", () => {
            return this.consumeTokenAndGetValue();
        })[0];
        this.ensureAndConsumeToken(";");
        if (currentDecl.checkUsingNameClash(names)) {
            this.raiseError(this.getCurrentLine(), "Collision between imported using names");
        }
        currentDecl.usings.push(new assembly_1.NamespaceUsing(fromns, names));
    }
    parseNamespaceTypedef(currentDecl) {
        //typedef NAME<T where C...> = TypeConstraint;
        this.ensureAndConsumeToken("typedef");
        this.ensureToken(TokenStrings.Type);
        const tyname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        this.ensureAndConsumeToken("=");
        const rpos = this.scanToken(";");
        if (rpos === this.m_epos) {
            this.raiseError(this.getCurrentLine(), "Missing ; on typedef");
        }
        const btype = this.parseTypeSignature();
        this.consumeToken();
        if (currentDecl.checkDeclNameClash(currentDecl.ns, tyname)) {
            this.raiseError(this.getCurrentLine(), "Collision between typedef and other names");
        }
        currentDecl.typeDefs.set(currentDecl.ns + "::" + tyname, new assembly_1.NamespaceTypedef(currentDecl.ns, tyname, terms, btype));
    }
    parseProvides(iscorens) {
        let provides = [];
        if (this.testToken("provides")) {
            this.consumeToken();
            while (!this.testToken("{") && !this.testToken(";")) {
                this.consumeTokenIf(",");
                provides.push(this.parseTypeSignature());
            }
        }
        else {
            if (!iscorens) {
                provides.push(new type_signature_1.NominalTypeSignature("NSCore", "Object"));
            }
        }
        return provides;
    }
    parseConstMember(staticMembers, allMemberNames, attributes, pragmas) {
        const sinfo = this.getCurrentSrcInfo();
        //[attr] const NAME[: T] = exp;
        this.ensureAndConsumeToken("const");
        this.ensureToken(TokenStrings.Identifier);
        const sname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(":");
        const stype = this.parseTypeSignature();
        let value = undefined;
        if (!Parser.attributeSetContains("abstract", attributes)) {
            this.ensureAndConsumeToken("=");
            value = this.parseExpression();
        }
        this.ensureAndConsumeToken(";");
        if (allMemberNames.has(sname)) {
            this.raiseError(this.getCurrentLine(), "Collision between const and other names");
        }
        allMemberNames.add(sname);
        staticMembers.set(sname, new assembly_1.StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, this.m_penv.getCurrentNamespace(), sname, stype, value));
    }
    parseStaticFunction(staticFunctions, allMemberNames, attributes, pragmas) {
        const sinfo = this.getCurrentSrcInfo();
        //[attr] static NAME<T where C...>(params): type [requires...] [ensures...] { ... }
        this.ensureAndConsumeToken("static");
        const termRestrictions = this.parseTermRestrictions();
        this.ensureToken(TokenStrings.Identifier);
        const fname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        let recursive = "no";
        if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
            recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
        }
        const sig = this.parseInvokableCommon(false, false, Parser.attributeSetContains("abstract", attributes), attributes, recursive, pragmas, terms, termRestrictions);
        if (allMemberNames.has(fname)) {
            this.raiseError(this.getCurrentLine(), "Collision between static and other names");
        }
        allMemberNames.add(fname);
        staticFunctions.set(fname, new assembly_1.StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), attributes, fname, sig));
    }
    parseMemberField(memberFields, allMemberNames, attributes, pragmas) {
        const sinfo = this.getCurrentSrcInfo();
        //[attr] field NAME[: T] = exp;
        this.ensureAndConsumeToken("field");
        this.ensureToken(TokenStrings.Identifier);
        const fname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(":");
        const stype = this.parseTypeSignature();
        let value = undefined;
        if (this.testAndConsumeTokenIf("=")) {
            value = this.parseExpression();
        }
        this.ensureAndConsumeToken(";");
        if (allMemberNames.has(fname)) {
            this.raiseError(this.getCurrentLine(), "Collision between const and other names");
        }
        memberFields.set(fname, new assembly_1.MemberFieldDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, fname, stype, value));
    }
    parseMemberMethod(thisType, memberMethods, allMemberNames, attributes, pragmas) {
        const sinfo = this.getCurrentSrcInfo();
        //[attr] method NAME<T where C...>(params): type [requires...] [ensures...] { ... }
        this.ensureAndConsumeToken("method");
        const termRestrictions = this.parseTermRestrictions();
        this.ensureToken(TokenStrings.Identifier);
        const mname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        let recursive = "no";
        if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
            recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
        }
        const sig = this.parseInvokableCommon(false, true, Parser.attributeSetContains("abstract", attributes), attributes, recursive, pragmas, terms, termRestrictions, thisType);
        if (allMemberNames.has(mname)) {
            this.raiseError(this.getCurrentLine(), "Collision between static and other names");
        }
        allMemberNames.add(mname);
        memberMethods.set(mname, new assembly_1.MemberMethodDecl(sinfo, this.m_penv.getCurrentFile(), attributes, mname, sig));
    }
    parseOOPMembersCommon(thisType, invariants, staticMembers, staticFunctions, memberFields, memberMethods) {
        while (this.testAndConsumeTokenIf("invariant")) {
            try {
                this.m_penv.pushFunctionScope(new parser_env_1.FunctionScope(new Set(["this"])));
                const body = this.parseExpression();
                this.ensureAndConsumeToken(";");
                invariants.push(body);
                this.m_penv.popFunctionScope();
            }
            catch (ex) {
                this.m_penv.popFunctionScope();
                throw ex;
            }
        }
        let allMemberNames = new Set();
        while (!this.testToken("}")) {
            const pragmas = this.parseDeclPragmas();
            const attributes = this.parseAttributes();
            if (this.testToken("const")) {
                this.parseConstMember(staticMembers, allMemberNames, attributes, pragmas);
            }
            else if (this.testToken("static")) {
                this.parseStaticFunction(staticFunctions, allMemberNames, attributes, pragmas);
            }
            else if (this.testToken("field")) {
                this.parseMemberField(memberFields, allMemberNames, attributes, pragmas);
            }
            else {
                this.ensureToken("method");
                this.parseMemberMethod(thisType, memberMethods, allMemberNames, attributes, pragmas);
            }
        }
    }
    parseConcept(currentDecl) {
        const line = this.getCurrentLine();
        //[attr] concept NAME[T where C...] provides {...}
        const pragmas = this.parseDeclPragmas();
        const attributes = this.parseAttributes();
        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken("concept");
        this.ensureToken(TokenStrings.Type);
        const cname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        const provides = this.parseProvides(currentDecl.ns === "NSCore");
        try {
            this.setRecover(this.scanCodeParens());
            this.ensureAndConsumeToken("{");
            const thisType = new type_signature_1.NominalTypeSignature(currentDecl.ns, cname, terms.map((term) => term.ttype));
            const invariants = [];
            const staticMembers = new Map();
            const staticFunctions = new Map();
            const memberFields = new Map();
            const memberMethods = new Map();
            this.parseOOPMembersCommon(thisType, invariants, staticMembers, staticFunctions, memberFields, memberMethods);
            this.ensureAndConsumeToken("}");
            if (currentDecl.checkDeclNameClash(currentDecl.ns, cname)) {
                this.raiseError(line, "Collision between concept and other names");
            }
            this.clearRecover();
            currentDecl.concepts.set(cname, new assembly_1.ConceptTypeDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, currentDecl.ns, cname, terms, provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods));
            this.m_penv.assembly.addConceptDecl(currentDecl.ns + "::" + cname, terms.length, currentDecl.concepts.get(cname));
        }
        catch (ex) {
            this.processRecover();
        }
    }
    parseObject(currentDecl) {
        const line = this.getCurrentLine();
        //[attr] object NAME[T where C...] provides {...}
        const pragmas = this.parseDeclPragmas();
        const attributes = this.parseAttributes();
        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken("entity");
        this.ensureToken(TokenStrings.Type);
        const cname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        const provides = this.parseProvides(currentDecl.ns === "NSCore");
        try {
            this.setRecover(this.scanCodeParens());
            this.ensureAndConsumeToken("{");
            const thisType = new type_signature_1.NominalTypeSignature(currentDecl.ns, cname, terms.map((term) => new type_signature_1.TemplateTypeSignature(term.name)));
            const invariants = [];
            const staticMembers = new Map();
            const staticFunctions = new Map();
            const memberFields = new Map();
            const memberMethods = new Map();
            this.parseOOPMembersCommon(thisType, invariants, staticMembers, staticFunctions, memberFields, memberMethods);
            this.ensureAndConsumeToken("}");
            if (currentDecl.checkDeclNameClash(currentDecl.ns, cname)) {
                this.raiseError(line, "Collision between object and other names");
            }
            this.clearRecover();
            currentDecl.concepts.set(cname, new assembly_1.EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, currentDecl.ns, cname, terms, provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods, false, false));
            this.m_penv.assembly.addObjectDecl(currentDecl.ns + "::" + cname, terms.length, currentDecl.concepts.get(cname));
        }
        catch (ex) {
            this.processRecover();
        }
    }
    parseNamespaceConst(currentDecl) {
        const sinfo = this.getCurrentSrcInfo();
        //[attr] const NAME[: T] = exp;
        const pragmas = this.parseDeclPragmas();
        const attributes = this.parseAttributes();
        this.ensureAndConsumeToken("global");
        this.ensureToken(TokenStrings.Identifier);
        const gname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(":");
        const gtype = this.parseTypeSignature();
        this.ensureAndConsumeToken("=");
        const value = this.parseExpression();
        this.ensureAndConsumeToken(";");
        if (currentDecl.checkDeclNameClash(currentDecl.ns, gname)) {
            this.raiseError(this.getCurrentLine(), "Collision between global and other names");
        }
        currentDecl.consts.set(gname, new assembly_1.NamespaceConstDecl(sinfo, this.m_penv.getCurrentFile(), pragmas, attributes, currentDecl.ns, gname, gtype, value));
    }
    parseNamespaceFunction(currentDecl) {
        const sinfo = this.getCurrentSrcInfo();
        //[attr] function NAME<T where C...>(params): type [requires...] [ensures...] { ... }
        const pragmas = this.parseDeclPragmas();
        const attributes = this.parseAttributes();
        this.ensureAndConsumeToken("function");
        this.ensureToken(TokenStrings.Identifier);
        const fname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        let recursive = "no";
        if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
            recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
        }
        const sig = this.parseInvokableCommon(false, false, false, attributes, recursive, pragmas, terms, []);
        currentDecl.functions.set(fname, new assembly_1.NamespaceFunctionDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, fname, sig));
    }
    parseEndOfStream() {
        this.ensureAndConsumeToken(TokenStrings.EndOfStream);
    }
    ////
    //Public methods
    parseCompilationUnitPass1(file, contents) {
        this.setNamespaceAndFile("[No Namespace]", file);
        const lexer = new Lexer(contents);
        this.initialize(lexer.lex());
        //namespace NS; ...
        this.ensureAndConsumeToken("namespace");
        this.ensureToken(TokenStrings.Namespace);
        const ns = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(";");
        this.setNamespaceAndFile(ns, file);
        const nsdecl = this.m_penv.assembly.ensureNamespace(ns);
        let parseok = true;
        while (this.m_cpos < this.m_epos) {
            try {
                this.m_cpos = this.scanTokenOptions("function", "global", "typedef", "concept", "entity", "enum", "identifier");
                if (this.m_cpos === this.m_epos) {
                    const tokenIndexBeforeEOF = this.m_cpos - 2;
                    if (tokenIndexBeforeEOF >= 0 && tokenIndexBeforeEOF < this.m_tokens.length) {
                        const tokenBeforeEOF = this.m_tokens[tokenIndexBeforeEOF];
                        if (tokenBeforeEOF.kind === TokenStrings.Error) {
                            this.raiseError(tokenBeforeEOF.line, `Expected */ but found EOF`);
                        }
                    }
                    break;
                }
                if (this.testToken("function") || this.testToken("global")) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.Identifier);
                    const fname = this.consumeTokenAndGetValue();
                    if (nsdecl.declaredNames.has(fname)) {
                        this.raiseError(this.getCurrentLine(), "Duplicate definition of name");
                    }
                    nsdecl.declaredNames.add(ns + "::" + fname);
                }
                else if (this.testToken("typedef") || this.testToken("concept") || this.testToken("entity") || this.testToken("enum") || this.testToken("identifier")) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.Type);
                    const tname = this.consumeTokenAndGetValue();
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), "Duplicate definition of name");
                    }
                    nsdecl.declaredNames.add(ns + "::" + tname);
                }
                else {
                    this.raiseError(this.getCurrentLine(), "Failed to parse top-level namespace declaration");
                }
            }
            catch (ex) {
                this.m_cpos++;
                parseok = false;
            }
        }
        return parseok;
    }
    parseCompilationUnitPass2(file, contents) {
        this.setNamespaceAndFile("[No Namespace]", file);
        const lexer = new Lexer(contents);
        this.initialize(lexer.lex());
        //namespace NS; ...
        this.ensureAndConsumeToken("namespace");
        this.ensureToken(TokenStrings.Namespace);
        const ns = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(";");
        this.setNamespaceAndFile(ns, file);
        const nsdecl = this.m_penv.assembly.ensureNamespace(ns);
        let usingok = true;
        let parseok = true;
        while (this.m_cpos < this.m_epos) {
            const rpos = this.scanTokenOptions("function", "global", "using", "typedef", "concept", "entity", "enum", "identifier", TokenStrings.EndOfStream);
            try {
                if (rpos === this.m_epos) {
                    break;
                }
                const tk = this.m_tokens[rpos].kind;
                usingok = usingok && tk === "using";
                if (tk === "using") {
                    if (!usingok) {
                        this.raiseError(this.getCurrentLine(), "Using statements must come before other declarations");
                    }
                    this.parseNamespaceUsing(nsdecl);
                }
                else if (tk === "function") {
                    this.parseNamespaceFunction(nsdecl);
                }
                else if (tk === "global") {
                    this.parseNamespaceConst(nsdecl);
                }
                else if (tk === "typedef") {
                    this.parseNamespaceTypedef(nsdecl);
                }
                else if (tk === "concept") {
                    this.parseConcept(nsdecl);
                }
                else if (tk === "entity") {
                    this.parseObject(nsdecl);
                }
                else if (tk === TokenStrings.EndOfStream) {
                    this.parseEndOfStream();
                }
                else {
                    //enum or identifier
                    this.raiseError(this.getCurrentLine(), "enum and identifier not implemented yet");
                }
            }
            catch (ex) {
                this.m_cpos = rpos + 1;
                parseok = false;
            }
        }
        return parseok;
    }
    getParseErrors() {
        return this.m_errors.length !== 0 ? this.m_errors.map((err) => `${err[1]} on line ${err[0]}`) : undefined;
    }
}
exports.Parser = Parser;
//# sourceMappingURL=parser.js.map