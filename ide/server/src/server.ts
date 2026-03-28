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

import {
  DiagnosticsService,
  NiceGeoSettings,
  DiagnosticsTriggerMode,
} from "./providers/diagnostics";

const STATUS_NOTIFICATION = "nicegeo/status";
const RUN_DIAGNOSTICS_NOTIFICATION = "nicegeo/runDiagnostics";

const connection = createConnection(ProposedFeatures.all);
const documents: TextDocuments<TextDocument> = new TextDocuments(TextDocument);

let hasConfigurationCapability = false;
let workspaceRoot: string | undefined;
const defaultSettings: NiceGeoSettings = { trigger: "onSave", debounceMs: 650 };
const documentSettings = new Map<string, Thenable<NiceGeoSettings>>();

function normalizeSettings(raw: unknown): NiceGeoSettings {
  const input = (raw ?? {}) as {
    diagnostics?: { trigger?: DiagnosticsTriggerMode; debounceMs?: number };
  };
  const trigger = input.diagnostics?.trigger;
  const debounceMs = input.diagnostics?.debounceMs;
  return {
    trigger: trigger === "onType" || trigger === "both" || trigger === "onSave" ? trigger : "onSave",
    debounceMs:
      Number.isFinite(debounceMs) && debounceMs !== undefined
        ? Math.max(100, Math.min(10_000, Math.floor(debounceMs)))
        : 650,
  };
}

function getDocumentSettings(resource: string): Thenable<NiceGeoSettings> {
  if (!hasConfigurationCapability) return Promise.resolve(defaultSettings);
  let result = documentSettings.get(resource);
  if (!result) {
    result = connection.workspace
      .getConfiguration({ scopeUri: resource, section: "nicegeo" })
      .then((cfg) => normalizeSettings(cfg));
    documentSettings.set(resource, result);
  }
  return result;
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
  const capabilities = params.capabilities;
  hasConfigurationCapability = !!capabilities.workspace?.configuration;
  workspaceRoot = params.rootUri ? fileURLToPath(params.rootUri) : undefined;

  return {
    capabilities: {
      textDocumentSync: TextDocumentSyncKind.Incremental,
    },
  };
});

connection.onInitialized(() => {
  connection.sendNotification(STATUS_NOTIFICATION, { kind: "idle" });
});

connection.onDidChangeConfiguration(() => {
  documentSettings.clear();
});

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

connection.onNotification(RUN_DIAGNOSTICS_NOTIFICATION, async (params: { uri?: string }) => {
  if (!params?.uri) return;
  const doc = documents.get(params.uri);
  if (!doc) return;
  diagnostics.runNow(doc, workspaceRoot);
});

connection.onShutdown(() => {
  diagnostics.dispose();
});

documents.listen(connection);
connection.listen();

