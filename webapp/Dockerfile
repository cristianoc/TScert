# The TScert-verified todo web app (webapp/app.ts is checked by
# `make check FILE=webapp/app.ts`; server.mts is the thin HTTP adapter).
# Node >= 23.6 strips types by default, so no build step is needed.
FROM node:26-slim
WORKDIR /app
COPY package.json app.ts server.mts ./
ENV PORT=8080
EXPOSE 8080
CMD ["node", "server.mts"]
