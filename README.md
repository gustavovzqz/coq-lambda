# Lambda Calculus in Coq

## Estrutura de Diretórios

- `theories/lambda/`: Contém as provas, propriedades e afins relacionadas ao cálculo lambda.
- `extraction/extraction.v`: Arquivo de extração em Coq.
- `lambda/`: Contém o código extraído para OCaml, incluindo um exemplo no arquivo 'bin/main.ml'.

## Compilação

### Na raiz do diretório

Para compilar o projeto, utilize o comando:

```bash
make
```

### Na pasta `lambda/`

Para compilar e executar o exemplo com o código extraído em OCaml, utilize os seguintes comandos:

```bash
dune build
dune exec lambda
```

