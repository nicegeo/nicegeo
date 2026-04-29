import {
  createConnection,
  ProposedFeatures,
  InitializeParams,
  InitializeResult,
  TextDocumentSyncKind,
  TextDocuments,
} from "vscode-languageserver/node";
import { TextDocument } from "vscode-languageserver-textdocument";
import { fileURLToPath } from "url";
import { DiagnosticsService, NiceGeoSettings, DiagnosticsTriggerMode } from "./providers/diagnostics";
import { runProofStateAt } from "./providers/proofstate";
import { provideCompletionItems, resolveCompletionItem } from "./providers/completion";

const STATUS_NOTIFICATION = "nicegeo/status";
const RUN_DIAGNOSTICS_NOTIFICATION = "nicegeo/runDiagnostics";
/** Custom LSP request: params `{ uri, line, col }` with VS Code 0-based line/character. */
const PROOF_STATE_AT_REQUEST = "nicegeo/proofStateAt";

const connection = createConnection(ProposedFeatures.all);
const documents: TextDocuments<TextDocument> = new TextDocuments(TextDocument);

let hasConfigurationCapability = false;
let workspaceRoot: string | undefined;
const defaultSettings: NiceGeoSettings = { trigger: "onSave", debounceMs: 650, executionMode: "dune" };
const documentSettings = new Map<string, Thenable<NiceGeoSettings>>();

function normalizeSettings(raw: unknown): NiceGeoSettings {
  const input = (raw ?? {}) as {
    diagnostics?: { trigger?: DiagnosticsTriggerMode; debounceMs?: number };
    execution?: { mode?: string };
  };
  const trigger = input.diagnostics?.trigger;
  const debounceMs = input.diagnostics?.debounceMs;
  const executionMode = input.execution?.mode;
  return {
    trigger: trigger === "onType" || trigger === "both" || trigger === "onSave" ? trigger : "onSave",
    debounceMs:
      Number.isFinite(debounceMs) && debounceMs !== undefined
        ? Math.max(100, Math.min(10_000, Math.floor(debounceMs)))
        : 650,
    executionMode: executionMode === "installedBinary" ? "installedBinary" : "dune",
  };
}

function getDocumentSettings(resource: string): Thenable<NiceGeoSettings> {
  if (!hasConfigurationCapability) return Promise.resolve(defaultSettings);
  const existing = documentSettings.get(resource);
  if (existing) return existing;
  const created = connection.workspace
    .getConfiguration({ scopeUri: resource, section: "nicegeo" })
    .then((cfg: unknown) => normalizeSettings(cfg));
  documentSettings.set(resource, created);
  return created;
}

const diagnostics = new DiagnosticsService(
  {
    checking: (_uri, detail) => connection.sendNotification(STATUS_NOTIFICATION, { kind: "checking", detail }),
    ok: (_uri) => connection.sendNotification(STATUS_NOTIFICATION, { kind: "ok" }),
    issues: (_uri, count) => connection.sendNotification(STATUS_NOTIFICATION, { kind: "issues", count }),
  },
  (uri, diags) => connection.sendDiagnostics({ uri, diagnostics: diags }),
);

connection.onInitialize((params: InitializeParams): InitializeResult => {
  hasConfigurationCapability = !!params.capabilities.workspace?.configuration;
  workspaceRoot = params.rootUri ? fileURLToPath(params.rootUri) : undefined;
  return {
    capabilities: {
      textDocumentSync: TextDocumentSyncKind.Incremental,
      completionProvider: {
        triggerCharacters: ["#", ".", " ", "(", ":", "-", "/", "\\"],
        resolveProvider: true,
      },
    },
  };
});

connection.onInitialized(() => connection.sendNotification(STATUS_NOTIFICATION, { kind: "idle" }));
connection.onDidChangeConfiguration(() => documentSettings.clear());

documents.onDidClose((e: { document: TextDocument }) => {
  documentSettings.delete(e.document.uri);
  diagnostics.clear(e.document.uri);
});

documents.onDidSave(async (e: { document: TextDocument }) => {
  const settings = await getDocumentSettings(e.document.uri);
  diagnostics.request(e.document, "save", settings, workspaceRoot);
});

documents.onDidChangeContent(async (e: { document: TextDocument }) => {
  const settings = await getDocumentSettings(e.document.uri);
  diagnostics.request(e.document, "type", settings, workspaceRoot);
});

connection.onNotification(RUN_DIAGNOSTICS_NOTIFICATION, (params: { uri?: string }) => {
  if (!params?.uri) return;
  const doc = documents.get(params.uri);
  if (!doc) return;
  void getDocumentSettings(params.uri).then((settings) => diagnostics.runNow(doc, settings, workspaceRoot));
});

connection.onRequest(
  PROOF_STATE_AT_REQUEST,
  async (params: { uri: string; line: number; col: number }) => {
    const settings = await getDocumentSettings(params.uri);
    return runProofStateAt(params.uri, params.line, params.col, workspaceRoot, settings);
  },
);

connection.onCompletion(async (params) => {
  if (hasConfigurationCapability) {
    const cfg = await connection.workspace.getConfiguration({
      scopeUri: params.textDocument.uri,
      section: "nicegeo.completion.enable",
    });
    if (cfg === false) return [];
  }
  const doc = documents.get(params.textDocument.uri);
  if (!doc) return [];
  return provideCompletionItems(doc, params.position.line, params.position.character, workspaceRoot);
});

connection.onCompletionResolve((item) => resolveCompletionItem(item));

connection.onShutdown(() => diagnostics.dispose());

documents.listen(connection);
connection.listen();
