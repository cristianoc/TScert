// webapp/server.mts — a thin Node HTTP adapter around the TScert-checked
// webapp/app.ts. This file is NOT part of the verified module; only app.ts is
// checked (`make check FILE=webapp/app.ts`). Run it with:
//
//   node webapp/server.mts
//
// then try:
//   node -e 'fetch("http://localhost:8080/todos", {method: "POST", body: "buy milk"}).then(r => r.text().then(t => console.log(r.status, t)))'

import { createServer } from "node:http";
import { handleRequest, initState } from "./app.ts";
import type { AppState, Request, Response } from "./app.ts";

let state: AppState = initState();

const server = createServer((req, res) => {
  let body = "";
  req.on("data", (chunk: Buffer) => {
    body += chunk.toString("utf8");
  });
  req.on("end", () => {
    const request: Request = {
      method: req.method ?? "GET",
      path: req.url ?? "/",
      body: body,
    };
    const [next, response]: [AppState, Response] = handleRequest(state, request);
    state = next;
    res.writeHead(response.status, { "content-type": response.contentType });
    res.end(response.body);
  });
});

const port = Number(process.env.PORT ?? 8080);

server.listen(port, "0.0.0.0", () => {
  console.log(`todo app listening on port ${port}`);
});
