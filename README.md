# baby-provas

O verificador de provas da **Baby AI** (app do Pedro Ferreira Pereira).

* `fila/` — provas em Lean escritas pela Baby (com um cérebro de IA), à espera de serem conferidas;
* `resultados/` — o que o Lean disse de cada uma (aceite ou o erro exato);
* `provadas/` — as provas que o Lean aceitou, guardadas inteiras (o ficheiro verificado e os selos);
* `varrimento/` — de 3 em 3 horas o Lean tenta sozinho, sem IA nenhuma, as táticas automáticas (decide, norm_num,
  simp, omega, positivity, linarith, nlinarith, aesop, exact?) em todos os teoremas, aos bocados;
* `catalogo/` — os teoremas por provar: os problemas de Erdős da lista pública da Google DeepMind
  ([formal-conjectures](https://github.com/google-deepmind/formal-conjectures), versão 04937a4ccc).

Uma prova só conta se o Lean não der erro, se o enunciado ficar letra a letra o original e se `#print axioms` mostrar
só `propext`, `Classical.choice` e `Quot.sound`. As provas são escritas com ajuda de modelos de IA.
