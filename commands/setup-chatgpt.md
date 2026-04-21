---
name: setup-chatgpt
description: Set up the ChatGPT MCP server for mathematical second opinions
---

# /setup-chatgpt - Set Up the ChatGPT MCP Server

Set up an MCP server that lets Claude Code query ChatGPT for mathematical
second opinions during Lean 4 formalization work.

## Usage

```
/setup-chatgpt
```

No arguments needed. This command will guide you through setup.

## What This Does

The `chatgpt-math` MCP server provides a single tool:

- `ask_chatgpt_math` - Ask ChatGPT a self-contained mathematics question.
  Useful for getting a second opinion on proof strategies, verifying
  mathematical claims, finding Mathlib API hints, or getting unstuck on
  formalization problems.

Parameters:
- `question` (required) - The mathematical question. Must be self-contained
  with all definitions, context, and notation included.
- `model` (optional) - Model to use. Default: `gpt-5.4`.
- `reasoning_effort` (optional) - `low`, `medium`, `high` (default), or `xhigh`.

## Prerequisites

1. **ChatGPT desktop app (Codex CLI)** - The server calls ChatGPT via the
   Codex CLI bundled with the ChatGPT desktop application.
   - macOS: Install from https://chatgpt.com/download (or the Mac App Store).
   - After install, the binary should be at:
     `/Applications/ChatGPT.app/Contents/Resources/codex`
     or `/Applications/Codex.app/Contents/Resources/codex`.
   - You must be signed in with a **ChatGPT Plus/Pro** subscription.

2. **Node.js** (>= 18) - The MCP server runs on Node.js.
   ```bash
   node --version   # Should be >= 18
   ```

## Setup Workflow

### Step 1: Find the Codex Binary

Locate the Codex CLI binary. Check these paths in order:
```bash
ls /Applications/ChatGPT.app/Contents/Resources/codex 2>/dev/null
ls /Applications/Codex.app/Contents/Resources/codex 2>/dev/null
```

If neither exists, tell the user to install the ChatGPT desktop app first.
Store the path as `CODEX_BIN`.

### Step 2: Create the MCP Server

Create the server directory and files:

```bash
mkdir -p ~/.claude/mcp-servers/chatgpt-math
```

Write the `package.json`:
```json
{
  "name": "chatgpt-math-mcp",
  "version": "1.0.0",
  "type": "module",
  "main": "server.js",
  "dependencies": {
    "@modelcontextprotocol/sdk": "^1.12.1"
  }
}
```

Write `server.js` (the MCP server implementation):
```javascript
import { Server } from "@modelcontextprotocol/sdk/server/index.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";
import {
  CallToolRequestSchema,
  ListToolsRequestSchema,
} from "@modelcontextprotocol/sdk/types.js";
import { execFile } from "node:child_process";
import { readFile, unlink } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";

const CODEX_BIN = "<CODEX_BIN_PATH>";
const DEFAULT_MODEL = "gpt-5.4";

const server = new Server(
  { name: "chatgpt-math", version: "2.0.0" },
  { capabilities: { tools: {} } }
);

server.setRequestHandler(ListToolsRequestSchema, async () => ({
  tools: [
    {
      name: "ask_chatgpt_math",
      description:
        "Ask ChatGPT (via Codex, using your ChatGPT Pro subscription) a mathematics " +
        "question. Use this when you need a second opinion on a proof strategy, want " +
        "to verify a mathematical claim, need hints about Mathlib API, or are stuck " +
        "on a formalization problem. The question must be fully self-contained since " +
        "ChatGPT has no access to local files.",
      inputSchema: {
        type: "object",
        properties: {
          question: {
            type: "string",
            description:
              "The mathematical question. Must be self-contained with all " +
              "definitions, context, and notation included.",
          },
          model: {
            type: "string",
            description:
              "Model to use. Default: gpt-5.4. Available: gpt-5.4, gpt-5.4-mini, " +
              "gpt-5.3-codex, etc.",
          },
          reasoning_effort: {
            type: "string",
            enum: ["low", "medium", "high", "xhigh"],
            description: "Reasoning effort level. Default: high.",
          },
        },
        required: ["question"],
      },
    },
  ],
}));

function runCodex(question, model, effort) {
  return new Promise((resolve, reject) => {
    const outFile = join(tmpdir(), `chatgpt-math-${Date.now()}.txt`);
    const args = [
      "exec", "--ephemeral", "--skip-git-repo-check",
      "-s", "read-only",
      "-m", model,
      "-c", `model_reasoning_effort="${effort}"`,
      "-o", outFile,
      question,
    ];
    execFile(CODEX_BIN, args, {
      timeout: 300_000,
      maxBuffer: 10 * 1024 * 1024,
      env: { ...process.env, NO_COLOR: "1" },
    }, async (err, stdout, stderr) => {
      try {
        const response = await readFile(outFile, "utf-8").catch(() => "");
        await unlink(outFile).catch(() => {});
        if (err && !response) {
          reject(new Error(`Codex failed: ${err.message}\nstderr: ${stderr}`));
          return;
        }
        resolve({ response: response.trim() || "(empty response)" });
      } catch (e) { reject(e); }
    });
  });
}

server.setRequestHandler(CallToolRequestSchema, async (request) => {
  if (request.params.name !== "ask_chatgpt_math") {
    return { content: [{ type: "text", text: `Unknown tool: ${request.params.name}` }], isError: true };
  }
  const { question, model, reasoning_effort } = request.params.arguments;
  const chosenModel = model || DEFAULT_MODEL;
  const effort = reasoning_effort || "high";
  const fullPrompt =
    "You are a research-level mathematics assistant. The user is working on " +
    "formal theorem proving in Lean 4 / Mathlib (algebraic geometry, adic spaces, " +
    "commutative algebra). Give precise, rigorous mathematical answers. " +
    "Reference specific Mathlib declarations when relevant. " +
    "Do NOT write or modify any files. Just answer the question.\n\n" +
    question;
  try {
    const { response } = await runCodex(fullPrompt, chosenModel, effort);
    return { content: [{ type: "text", text: `## ChatGPT Response (${chosenModel}, effort: ${effort})\n\n${response}` }] };
  } catch (err) {
    return { content: [{ type: "text", text: `Error calling ChatGPT via Codex: ${err.message}` }], isError: true };
  }
});

async function main() {
  const transport = new StdioServerTransport();
  await server.connect(transport);
  console.error("chatgpt-math MCP server v2 running (via Codex CLI)");
}
main().catch((err) => { console.error("Fatal error:", err); process.exit(1); });
```

**Important:** Replace `<CODEX_BIN_PATH>` in `server.js` with the actual path
found in Step 1 (e.g., `/Applications/ChatGPT.app/Contents/Resources/codex`).

### Step 3: Install Dependencies

```bash
cd ~/.claude/mcp-servers/chatgpt-math && npm install
```

### Step 4: Configure MCP Server

Add the `chatgpt-math` server to the **project-level** `.mcp.json` in the
user's current working directory.

Read the existing `.mcp.json` if it exists (to preserve other servers), then
add or update the `chatgpt-math` entry:

```json
{
  "mcpServers": {
    "chatgpt-math": {
      "type": "stdio",
      "command": "node",
      "args": ["<HOME>/.claude/mcp-servers/chatgpt-math/server.js"],
      "env": {}
    }
  }
}
```

Replace `<HOME>` with the user's actual home directory path.

If `.mcp.json` already exists with other servers, **merge** the new entry --
don't overwrite existing servers.

### Step 5: Verify

Test that the Codex CLI works by running a simple query:
```bash
echo "What is 2+2?" | <CODEX_BIN> exec --ephemeral --skip-git-repo-check -s read-only -m gpt-5.4 -
```

If this returns a response, the setup is working.

### Step 6: Report

Tell the user:
1. The MCP server has been configured.
2. They need to **restart Claude Code** (or reload MCP servers) for the new
   server to take effect.
3. After restart, they can use `ask_chatgpt_math` to query ChatGPT for
   mathematical assistance during Lean 4 work.
4. The system prompt is pre-configured for Lean 4 / Mathlib / algebraic
   geometry context -- questions should still be self-contained since ChatGPT
   has no access to local files.

## Customization

### System Prompt

The default system prompt targets Lean 4 / Mathlib formalization. To
customize, edit the `fullPrompt` construction in `server.js`.

### Default Model

Change `DEFAULT_MODEL` in `server.js` to use a different ChatGPT model by
default.

## Troubleshooting

### "Codex failed" or binary not found

Make sure the ChatGPT desktop app is installed and you're signed in.
Check that the binary path in `server.js` matches your installation:
```bash
find /Applications -name "codex" -type f 2>/dev/null
```

### "npm install" fails

Make sure Node.js >= 18 is installed:
```bash
node --version
npm --version
```

### Server not appearing in Claude Code

1. Check that `.mcp.json` is in the project root.
2. Restart Claude Code after adding the config.
3. Verify the path in `.mcp.json` is absolute and correct.
4. Check that `node ~/.claude/mcp-servers/chatgpt-math/server.js` runs
   without errors (it should print to stderr and wait for stdin).

### Rate limits or empty responses

ChatGPT has its own rate limits. If you get empty responses, wait a moment
and try again. The 5-minute timeout is generous for most queries.
