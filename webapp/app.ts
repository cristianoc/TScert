// webapp/app.ts — the core of a tiny todo web app, written entirely in
// TScert's verified fragment: every exported function is annotated, nothing
// is `any`, and no assertion (`as` / `!`) decides a type. The state is plain
// data and every update returns a fresh value, so the verifier can prove each
// function safe. Check it with:
//
//   make check FILE=webapp/app.ts
//
// webapp/server.mts is the thin Node HTTP adapter around handleRequest; it is
// not part of the checked module.

export interface Todo {
  id: number;
  title: string;
  done: boolean;
}

export interface AppState {
  nextId: number;
  todos: Todo[];
}

export interface Request {
  method: string;
  path: string;
  body: string;
}

export interface Response {
  status: number;
  body: string;
}

// JSON.stringify's parameter is read at this library type (SOURCE-CONTRACTS):
// a record typed by its fields is not a JsonValue, so the app converts its
// data to one explicitly.
export type JsonValue =
  | null
  | boolean
  | number
  | string
  | readonly JsonValue[]
  | { readonly [key: string]: JsonValue };

export function initState(): AppState {
  return { nextId: 1, todos: [] };
}

export function addTodo(state: AppState, title: string): AppState {
  const todo: Todo = { id: state.nextId, title: title, done: false };
  const todos: Todo[] = state.todos.slice();
  todos.push(todo);
  return { nextId: state.nextId + 1, todos: todos };
}

export function toggleTodo(state: AppState, id: number): AppState {
  const todos: Todo[] = state.todos.map((todo) =>
    todo.id === id ? { id: todo.id, title: todo.title, done: !todo.done } : todo,
  );
  return { nextId: state.nextId, todos: todos };
}

export function deleteTodo(state: AppState, id: number): AppState {
  return { nextId: state.nextId, todos: state.todos.filter((todo) => todo.id !== id) };
}

// A decimal id, or -1 when the text is empty or holds a non-digit.
export function parseId(text: string): number {
  if (text.length === 0) {
    return -1;
  }
  let n: number = 0;
  let i: number = 0;
  while (i < text.length) {
    const c: number = text.charCodeAt(i);
    if (c < 48 || c > 57) {
      return -1;
    }
    n = n * 10 + (c - 48);
    i = i + 1;
  }
  return n;
}

export function escapeHtml(text: string): string {
  let out: string = "";
  let i: number = 0;
  while (i < text.length) {
    const c: string = text.charAt(i);
    if (c === "&") {
      out = out + "&amp;";
    } else if (c === "<") {
      out = out + "&lt;";
    } else if (c === ">") {
      out = out + "&gt;";
    } else {
      out = out + c;
    }
    i = i + 1;
  }
  return out;
}

export function renderPage(state: AppState): string {
  let items: string = "";
  for (const todo of state.todos) {
    const mark: string = todo.done ? "[x]" : "[ ]";
    items = items + `<li>${mark} ${escapeHtml(todo.title)} (id ${todo.id})</li>`;
  }
  return `<!doctype html><html><head><title>todos</title></head><body><h1>Todos</h1><ul>${items}</ul></body></html>`;
}

export function todoJson(todo: Todo): JsonValue {
  return { id: todo.id, title: todo.title, done: todo.done };
}

export function todosJson(todos: Todo[]): JsonValue {
  return todos.map((todo) => todoJson(todo));
}

function jsonOk(state: AppState): Response {
  return { status: 200, body: JSON.stringify(todosJson(state.todos)) };
}

function badRequest(message: string): Response {
  return { status: 400, body: message };
}

function notFound(): Response {
  return { status: 404, body: "not found" };
}

// The router: one pure function from (state, request) to (next state, response).
export function handleRequest(state: AppState, req: Request): [AppState, Response] {
  if (req.method === "GET" && req.path === "/") {
    return [state, { status: 200, body: renderPage(state) }];
  }
  if (req.method === "GET" && req.path === "/todos") {
    return [state, jsonOk(state)];
  }
  if (req.method === "POST" && req.path === "/todos") {
    const next: AppState = addTodo(state, req.body);
    return [next, { status: 201, body: JSON.stringify(todosJson(next.todos)) }];
  }
  if (req.method === "POST" && req.path.startsWith("/todos/") && req.path.endsWith("/toggle")) {
    const id: number = parseId(req.path.slice("/todos/".length, req.path.length - "/toggle".length));
    if (id < 0) {
      return [state, badRequest("bad id")];
    }
    const next: AppState = toggleTodo(state, id);
    return [next, jsonOk(next)];
  }
  if (req.method === "DELETE" && req.path.startsWith("/todos/")) {
    const id: number = parseId(req.path.slice("/todos/".length));
    if (id < 0) {
      return [state, badRequest("bad id")];
    }
    const next: AppState = deleteTodo(state, id);
    return [next, jsonOk(next)];
  }
  if (req.method === "GET" && req.path.startsWith("/todos/")) {
    const id: number = parseId(req.path.slice("/todos/".length));
    if (id < 0) {
      return [state, badRequest("bad id")];
    }
    const matches: Todo[] = state.todos.filter((todo) => todo.id === id);
    if (matches.length === 0) {
      return [state, notFound()];
    }
    return [state, { status: 200, body: JSON.stringify(todosJson(matches)) }];
  }
  return [state, notFound()];
}
