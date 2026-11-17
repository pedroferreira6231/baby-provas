"""15/11/2026 — O VERIFICADOR DE PROVAS DA BABY (Lean 4 + Mathlib), no telemóvel do Pedro.

Pedro (15/11): "tens que o ensinar a fazer essas provas … estás sempre a limitar o baby" — e escolheu correr o Lean
"no Redmi 15 Pro". Corre no Termux, dentro do Ubuntu do proot-distro (instalado por instalar_lean.sh), e a app fala
com ele em http://127.0.0.1:8090 (como já fazia com o llama-server da voz).

Os problemas são os da lista pública da Google DeepMind (github.com/google-deepmind/formal-conjectures): os problemas
de Erdős já escritos em Lean, cada um com `:= by sorry` no lugar da prova. A Baby (com um cérebro) escreve uma prova;
este servidor:
  1. pega no ficheiro ORIGINAL do problema e troca só o `sorry` daquele teorema pela prova — o enunciado não muda;
  2. aceita lemas auxiliares, mas só teoremas, lemas e definições (nada de `instance`, `notation`, `open`,
     `variable`, `axiom`… que pudessem mudar o sentido do enunciado);
  3. corre o Lean, e no fim `#print axioms`: a prova só conta se o Lean não der erro E o teorema depender apenas dos
     três axiomas de sempre (propext, Classical.choice, Quot.sound) — um `sorry` escondido ou um `native_decide`
     aparecem aqui e a prova é recusada;
  4. guarda cada prova aceite (o ficheiro inteiro) em ~/fc/BabyProvas/provadas/.

Só usa a biblioteca normal do Python. Um Lean de cada vez (é pesado: 2 a 4 GB de memória).

17/11/2026 (1.56, o Pedro escolheu "B": o Lean sai do telemóvel e vai para os computadores grátis do GitHub): o mesmo
ficheiro corre também no GitHub, sem servidor, em dois modos:
  python3 servidor_lean.py --catalogo DIR                — escreve o catálogo (indice.json + um ficheiro por problema)
  python3 servidor_lean.py --lote FILA RESULTADOS PROVADAS — confere cada prova da fila, escreve o resultado e apaga-a
A cópia que a app envia para o GitHub é reasoning/verificador_lean.py (tem de ser igual a esta: há um teste).
"""
import hashlib
import json
import os
import re
import subprocess
import textwrap
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse

VERSAO = "1.56"
RAIZ = Path(os.environ.get("BABY_FC", str(Path.home() / "fc")))
PORTA = int(os.environ.get("BABY_LEAN_PORTA", "8090"))
TEMPO = int(os.environ.get("BABY_LEAN_TEMPO", "900"))         # segundos para uma verificação
PASTA = "BabyProvas"
PROBLEMAS = "FormalConjectures/ErdosProblems"
AXIOMAS_OK = {"propext", "Classical.choice", "Quot.sound"}

# 15/11 (1.53): o enunciado NUNCA pode atravessar outra declaração — na 1.52 um teorema já provado podia "colar-se"
# ao `sorry` de um teorema seguinte (e o #print axioms olharia para o errado). Agora pára em qualquer linha que comece
# uma declaração nova e em qualquer `:= by` (o início de uma prova).
_NAO_ATRAVESSA = (r"(?:(?!\n[ \t]*(?:@\[|/--|theorem\b|lemma\b|def\b|noncomputable\b|abbrev\b|instance\b|example\b|"
                  r"namespace\b|end\b|open\b|variable\b|section\b|structure\b|inductive\b|class\b|private\b|"
                  r"protected\b|set_option\b))(?!:=\s*by\b).)")
RE_TEOREMA = re.compile(
    r"(?P<doc>/--(?:(?!-/).)*?-/\s*)?(?P<pre>(?:set_option[^\n]*\n\s*)*)"
    r"@\[category (?P<cat>[a-z ]+?)[,\]][^\n]*\n\s*(?:theorem|lemma)\s+(?P<nome>[^\s:(\[{]+)(?P<tipo>"
    + _NAO_ATRAVESSA + r"*?)"
    r":=\s*by(?P<sep>[ \t]*\n(?P<ind>[ \t]*)|[ \t]+)sorry\b", re.S)
RE_DEF_SORRY = re.compile(r"(?m)^\s*(?:noncomputable\s+)?(?:def|abbrev)\s+([^\s:(\[{]+)[^\n]*:=\s*sorry\s*$")

# palavras que nunca podem aparecer (em lado nenhum da resposta)
PROIBIDO = ("sorry", "admit", "native_decide", "axiom", "unsafe", "implemented_by", "extern", "run_tac", "run_cmd",
            "run_elab", "#eval", "import", "elab", "macro", "syntax", "notation", "infix", "prefix", "postfix",
            "instance", "attribute", "open", "export", "namespace", "section", "variable", "include", "omit",
            "universe", "opaque", "Lean.", "debug.", "ofReduceBool", "trustCompiler", "decide := true",
            "set_option", "local", "scoped", "@[expose]", "module", "public", "meta")
# nas linhas de topo dos auxiliares só podem começar estas coisas (o resto tem de estar indentado)
TOPO_OK = re.compile(r"^(?:(?:private|protected|noncomputable|theorem|lemma|def|abbrev)\b|@\[simp\]|/--|--|-/|$)")
# dentro da prova (tática) estas são aceites: só mudam limites de tempo do Lean
PROVA_OK_SET_OPTION = re.compile(r"set_option\s+(?:maxHeartbeats|maxRecDepth|synthInstance\.maxHeartbeats)\s+\d+\s+in")


def _palavras(texto):
    """As palavras proibidas que aparecem no texto (fora de comentários de linha)."""
    sem_coment = re.sub(r"--[^\n]*", "", texto)
    sem_coment = re.sub(r"/-(?:(?!-/).)*-/", "", sem_coment, flags=re.S)
    achadas = []
    for p in PROIBIDO:
        if p[0].isalpha() or p[0] == "#":
            if re.search(r"(?<![\w.'])" + re.escape(p) + r"(?![\w'])", sem_coment):
                achadas.append(p)
        elif p in sem_coment:
            achadas.append(p)
    return achadas


# ------------------------------------------------------------------ o catálogo
def catalogo(raiz=RAIZ):
    """Todos os teoremas com `:= by sorry` dos problemas de Erdős: {id: {...}}."""
    out = {}
    for f in sorted((Path(raiz) / PROBLEMAS).glob("*.lean"), key=lambda p: (len(p.stem), p.stem)):
        try:
            s = f.read_text(encoding="utf-8")
        except OSError:
            continue
        # 15/11: as "respostas" ainda por preencher (`def erdos_X.answer … := sorry`) — os teoremas que as usam não
        # se podem provar sem mudar o enunciado: ficam de fora
        respostas = {n.split(".")[-1] for n in RE_DEF_SORRY.findall(s)} | set(RE_DEF_SORRY.findall(s))
        for m in RE_TEOREMA.finditer(s):
            if respostas and re.search(r"(?<![\w'])(?:" + "|".join(re.escape(r) for r in respostas) + r")(?![\w'])",
                                       m.group("tipo")):
                continue
            ident = f"{f.stem}:{m.group('nome')}"
            doc = (m.group("doc") or "").strip()
            doc = doc[3:-2].strip() if doc.startswith("/--") else doc
            out[ident] = {"id": ident, "numero": f.stem, "nome": m.group("nome"), "categoria": m.group("cat").strip(),
                          "enunciado": ("theorem " + m.group("nome") + m.group("tipo")).strip(),
                          "doc": doc, "ficheiro": str(f.relative_to(raiz)), "linha": s[:m.start()].count("\n") + 1}
    return out


def contexto(raiz, alvo, maximo=5000):
    """O que está no ficheiro antes do teorema (definições, `open`, namespace), sem a licença."""
    s = (Path(raiz) / alvo["ficheiro"]).read_text(encoding="utf-8")
    m = _achar(s, alvo["nome"])
    antes = s[:m.start()] if m else s
    antes = re.sub(r"^/-\s*Copyright.*?-/\s*", "", antes, flags=re.S)
    return antes[-maximo:]


def _achar(s, nome):
    for m in RE_TEOREMA.finditer(s):
        if m.group("nome") == nome:
            return m
    return None


# ------------------------------------------------------------------ montar o ficheiro
class Recusada(ValueError):
    pass


def limpar_prova(prova):
    p = str(prova or "").strip("\n")
    p = textwrap.dedent(p).strip("\n")
    if re.match(r"^\s*by\b", p):                                   # o cérebro escreveu "by …"
        p = textwrap.dedent(re.sub(r"^\s*by\b[ \t]*\n?", "", p, count=1)).strip("\n")
    return p


def montar(texto_original, alvo, prova, auxiliares=""):
    """O ficheiro original com o `sorry` do alvo trocado pela prova, os auxiliares antes do teorema e o
    `#print axioms` logo a seguir. Levanta Recusada se a resposta tiver coisas proibidas."""
    prova = limpar_prova(prova)
    aux = textwrap.dedent(str(auxiliares or "")).strip("\n")
    if not prova.strip():
        raise Recusada("a prova vem vazia")
    if len(prova) + len(aux) > 30000:
        raise Recusada("a prova é grande de mais (mais de 30 000 letras)")
    sem_set = PROVA_OK_SET_OPTION.sub("", prova)
    mal = sorted(set(_palavras(sem_set) + _palavras(aux)))
    if mal:
        raise Recusada("a resposta usa coisas proibidas: " + ", ".join(mal))
    for linha in aux.split("\n"):
        if linha and not linha[0].isspace() and not TOPO_OK.match(linha):
            raise Recusada(f"nos lemas auxiliares só são aceites teoremas, lemas e definições: «{linha[:60]}»")
    m = _achar(texto_original, alvo["nome"])
    if m is None:
        raise Recusada("não encontrei o teorema no ficheiro original")
    ind = m.group("ind") or "  "
    corpo = "\n" + textwrap.indent(prova, ind)
    inicio = m.start("doc") if m.group("doc") else m.start("pre") if m.group("pre") else m.start()
    fim_sorry = m.end()
    cabeca = texto_original[inicio:m.start("sep")]                    # docstring, atributos e o enunciado
    novo = (texto_original[:inicio] + (aux + "\n\n" if aux else "") + cabeca
            + corpo + f"\n\n#print axioms {alvo['nome']}\n" + texto_original[fim_sorry:])
    # 15/11 (GPT): conferir que o enunciado ficou letra a letra igual ao original, e o resto do ficheiro também
    k = novo.find(cabeca, len(texto_original[:inicio]))
    if k < 0 or novo[:inicio] != texto_original[:inicio] or not novo.endswith(texto_original[fim_sorry:]):
        raise Recusada("o enunciado ou o resto do ficheiro mudou ao montar a prova")
    return novo


def sha(texto):
    return hashlib.sha256(texto.encode("utf-8")).hexdigest()


# ------------------------------------------------------------------ ler o que o Lean diz
RE_CABECA = re.compile(r"^(?P<f>[^\n:]+):(?P<l>\d+):(?P<c>\d+): (?P<tipo>error|warning|info)(?:\([^)]*\))?:", re.M)


def ler_saida(saida, nome):
    erros, axiomas = [], None
    cabecas = list(RE_CABECA.finditer(saida))
    for i, c in enumerate(cabecas):
        fim = cabecas[i + 1].start() if i + 1 < len(cabecas) else len(saida)
        bloco = saida[c.start():fim].strip()
        if c.group("tipo") == "error":
            erros.append(bloco)
    curto = re.escape(nome.split(".")[-1])
    m = re.search(r"'(?P<n>[^']*" + curto + r")' depends on axioms: \[(?P<ax>[^\]]*)\]", saida)
    if m:
        axiomas = [a.strip() for a in m.group("ax").split(",") if a.strip()]
    elif re.search(r"'[^']*" + curto + r"' does not depend on any axioms", saida):
        axiomas = []
    if not cabecas and "error" in saida.lower() and axiomas is None:
        erros.append(saida.strip()[-1500:])
    return erros, axiomas


def veredicto(erros, axiomas):
    if erros:
        return False, "o Lean encontrou erros"
    if axiomas is None:
        return False, "o Lean não disse de que axiomas a prova depende"
    estranhos = [a for a in axiomas if a not in AXIOMAS_OK]
    if estranhos:
        return False, "a prova depende de axiomas não aceites: " + ", ".join(estranhos)
    return True, "PROVADA: o Lean aceitou a prova e só usa os axiomas de sempre"


# ------------------------------------------------------------------ o servidor
class Verificador:
    def __init__(self, raiz=RAIZ, correr=None, tempo=TEMPO):
        self.raiz = Path(raiz)
        self.tempo = tempo
        self.correr = correr or self._correr_lean
        self.trinco = threading.Lock()
        self.ocupado = False
        self.alvos = catalogo(self.raiz)
        self.contas = {"verificadas": 0, "provadas": 0, "recusadas": 0}
        self.ultima = None
        self.lean = self._versao()
        self.commit = self._commit()

    def _versao(self):
        try:
            r = subprocess.run(["lake", "env", "lean", "--version"], cwd=self.raiz, capture_output=True, text=True,
                               timeout=120)
            return (r.stdout or r.stderr).strip()[:120]
        except (OSError, subprocess.SubprocessError):
            return None

    def _commit(self):
        try:
            return subprocess.run(["git", "rev-parse", "HEAD"], cwd=self.raiz, capture_output=True, text=True,
                                  timeout=30).stdout.strip()[:40] or None
        except (OSError, subprocess.SubprocessError):
            return None

    def _correr_lean(self, ficheiro):
        r = subprocess.run(["lake", "env", "lean", str(ficheiro)], cwd=self.raiz, capture_output=True, text=True,
                           timeout=self.tempo)
        return r.returncode, (r.stdout or "") + (r.stderr or "")

    def estado(self):
        return {"ok": True, "versao": VERSAO, "lean": self.lean, "commit": self.commit, "alvos": len(self.alvos),
                "ocupado": self.ocupado, **self.contas, "ultima": self.ultima}

    def verificar(self, ident, prova, auxiliares=""):
        alvo = self.alvos.get(ident)
        if not alvo:
            return {"ok": False, "provada": False, "erro": f"não conheço o problema «{ident}»"}
        if not self.trinco.acquire(blocking=False):
            return {"ok": False, "provada": False, "erro": "ocupado: o Lean já está a verificar outra prova"}
        self.ocupado = True
        t0 = time.time()
        try:
            original = (self.raiz / alvo["ficheiro"]).read_text(encoding="utf-8")
            try:
                texto = montar(original, alvo, prova, auxiliares)
            except Recusada as ex:
                self.contas["recusadas"] += 1
                r = {"ok": True, "provada": False, "recusada": True, "erro": str(ex), "segundos": 0}
                self.ultima = {"id": ident, "quando": time.strftime("%Y-%m-%d %H:%M"), "provada": False,
                               "erro": str(ex)[:200]}
                return r
            pasta = self.raiz / PASTA
            pasta.mkdir(exist_ok=True)
            nome_f = f"T{int(t0)}_{re.sub(r'[^A-Za-z0-9]', '_', ident)}.lean"
            ficheiro = pasta / nome_f
            ficheiro.write_text(texto, encoding="utf-8")
            try:
                codigo, saida = self.correr(ficheiro.relative_to(self.raiz))
            except subprocess.TimeoutExpired:
                codigo, saida = -1, f"error: passou o tempo ({self.tempo} s) — o Lean não acabou"
            erros, axiomas = ler_saida(saida, alvo["nome"])
            if codigo == -1 and not erros:
                erros = [saida]
            provada, porque = veredicto(erros, axiomas)
            self.contas["verificadas"] += 1
            selos = {"lean": self.lean, "commit": self.commit, "sha_original": sha(original),
                     "sha_verificado": sha(texto), "ficheiro": alvo["ficheiro"]}
            if provada:
                self.contas["provadas"] += 1
                (pasta / "provadas").mkdir(exist_ok=True)
                (pasta / "provadas" / nome_f).write_text(texto, encoding="utf-8")
                (pasta / "provadas" / (nome_f[:-5] + ".json")).write_text(
                    json.dumps(dict(selos, id=ident, axiomas=axiomas, quando=time.strftime("%Y-%m-%d %H:%M"),
                                    segundos=round(time.time() - t0, 1)), ensure_ascii=False), encoding="utf-8")
            try:
                ficheiro.unlink()
            except OSError:
                pass
            r = {"ok": True, "provada": provada, "porque": porque, "axiomas": axiomas,
                 "erro": "\n\n".join(erros)[:3000] if erros else None, "segundos": round(time.time() - t0, 1),
                 "commit": self.commit, "selos": selos}
            self.ultima = {"id": ident, "quando": time.strftime("%Y-%m-%d %H:%M"), "provada": provada,
                           "erro": porque if provada else (r["erro"] or porque)[:200]}
            return r
        finally:
            self.ocupado = False
            self.trinco.release()


def criar_servidor(verificador, porta=PORTA):
    class H(BaseHTTPRequestHandler):
        def log_message(self, *a):
            pass

        def _json(self, codigo, d):
            corpo = json.dumps(d, ensure_ascii=False).encode("utf-8")
            self.send_response(codigo)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Content-Length", str(len(corpo)))
            self.end_headers()
            self.wfile.write(corpo)

        def do_GET(self):
            u = urlparse(self.path)
            if u.path == "/estado":
                return self._json(200, verificador.estado())
            if u.path == "/alvos":
                return self._json(200, {"ok": True, "alvos": [{k: a[k] for k in ("id", "numero", "nome", "categoria")}
                                                              for a in verificador.alvos.values()]})
            if u.path == "/alvo":
                ident = (parse_qs(u.query).get("id") or [""])[0]
                a = verificador.alvos.get(ident)
                if not a:
                    return self._json(404, {"ok": False, "erro": "não conheço esse problema"})
                return self._json(200, dict(a, ok=True, contexto=contexto(verificador.raiz, a)))
            return self._json(404, {"ok": False})

        def do_POST(self):
            if urlparse(self.path).path != "/verificar":
                return self._json(404, {"ok": False})
            try:
                n = int(self.headers.get("Content-Length") or 0)
                d = json.loads(self.rfile.read(min(n, 200000)).decode("utf-8") or "{}")
            except (ValueError, OSError):
                return self._json(400, {"ok": False, "erro": "pedido mal escrito"})
            r = verificador.verificar(str(d.get("id") or ""), d.get("prova"), d.get("auxiliares") or "")
            return self._json(200 if r.get("ok") else 409, r)

    return ThreadingHTTPServer(("127.0.0.1", porta), H)


# ------------------------------------------------------------------ 1.56: o modo GitHub (sem servidor)
def escrever_catalogo(raiz, pasta, commit=None):
    alvos = catalogo(raiz)
    pasta = Path(pasta)
    pasta.mkdir(parents=True, exist_ok=True)
    por = {}
    for a in alvos.values():
        por.setdefault(a["numero"], []).append(dict(a, contexto=contexto(raiz, a)))
    for n, lista in por.items():
        (pasta / f"{n}.json").write_text(json.dumps(lista, ensure_ascii=False), encoding="utf-8")
    indice = [{k: a[k] for k in ("id", "numero", "nome", "categoria")} for a in alvos.values()]
    (pasta / "indice.json").write_text(json.dumps({"commit": commit, "versao": VERSAO, "alvos": indice},
                                                  ensure_ascii=False), encoding="utf-8")
    return len(indice)


def lote(v, fila, resultados, provadas):
    """Confere cada prova de FILA/*.json; o resultado vai para RESULTADOS/<o mesmo nome>; as aceites ficam inteiras
    em PROVADAS/. Devolve quantas conferiu."""
    fila, resultados, provadas = Path(fila), Path(resultados), Path(provadas)
    resultados.mkdir(parents=True, exist_ok=True)
    n = 0
    for f in sorted(fila.glob("*.json")):
        try:
            d = json.loads(f.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            d = {}
        r = v.verificar(str(d.get("id") or ""), d.get("prova"), d.get("auxiliares") or "")
        r["pedido"] = {k: d.get(k) for k in ("id", "selo", "cerebro", "quando")}
        r["verificada_em"] = time.strftime("%Y-%m-%d %H:%M UTC", time.gmtime())
        if r.get("provada"):
            provadas.mkdir(parents=True, exist_ok=True)
            for g in sorted((v.raiz / PASTA / "provadas").glob("*")):
                if not (provadas / g.name).exists():
                    (provadas / g.name).write_bytes(g.read_bytes())
        (resultados / f.name).write_text(json.dumps(r, ensure_ascii=False), encoding="utf-8")
        f.unlink()
        n += 1
        print(f"{f.name}: {'PROVADA' if r.get('provada') else 'recusada'} ({r.get('segundos')} s)", flush=True)
    return n


if __name__ == "__main__":
    import sys
    if len(sys.argv) >= 3 and sys.argv[1] == "--catalogo":
        v = Verificador()
        print("catálogo:", escrever_catalogo(v.raiz, sys.argv[2], v.commit), "teoremas", flush=True)
        sys.exit(0)
    if len(sys.argv) >= 5 and sys.argv[1] == "--lote":
        v = Verificador()
        print("conferidas:", lote(v, sys.argv[2], sys.argv[3], sys.argv[4]), flush=True)
        sys.exit(0)
    v = Verificador()
    print(f"Verificador de provas da Baby {VERSAO} · {v.lean} · formal-conjectures {str(v.commit)[:10]} · "
          f"{len(v.alvos)} teoremas por provar · http://127.0.0.1:{PORTA}", flush=True)
    criar_servidor(v).serve_forever()
