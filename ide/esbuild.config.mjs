import esbuild from "esbuild";
import { rm } from "node:fs/promises";

const args = new Set(process.argv.slice(2));
const isProduction = args.has("--production");
const isWatch = args.has("--watch");
const isClean = args.has("--clean");

const shared = {
  bundle: true,
  sourcemap: isProduction ? false : true,
  minify: isProduction,
  target: "es2022",
  logLevel: "info",
};

const extensionBuild = {
  ...shared,
  entryPoints: ["client/extension.ts"],
  outfile: "out/extension.js",
  platform: "node",
  format: "cjs",
  external: ["vscode"],
};

const serverBuild = {
  ...shared,
  entryPoints: ["server/src/server.ts"],
  outfile: "server/out/server.js",
  platform: "node",
  format: "cjs",
};

const webviewBuild = {
  ...shared,
  entryPoints: ["client/visual/index.ts"],
  outfile: "out/visual/index.js",
  platform: "browser",
  format: "esm",
};

const allBuilds = [extensionBuild, serverBuild, webviewBuild];
const cleanPaths = ["out", "server/out"];

async function buildAll() {
  await Promise.all(allBuilds.map((config) => esbuild.build(config)));
}

async function watchAll() {
  const contexts = await Promise.all(allBuilds.map((config) => esbuild.context(config)));
  await Promise.all(contexts.map((ctx) => ctx.watch()));
  console.log("Watching extension, server, and webview builds...");
}

async function cleanAll() {
  await Promise.all(cleanPaths.map((path) => rm(path, { recursive: true, force: true })));
  console.log("Cleaned build artifacts: out, server/out");
}

if (isClean) {
  await cleanAll();
} else if (isWatch) {
  await watchAll();
} else {
  await buildAll();
}
