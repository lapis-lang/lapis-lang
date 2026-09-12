# Contributing to Lapis

Thanks for your interest in contributing! This project is written in
[TypeScript](https://www.typescriptlang.org) and runs on [Deno](https://deno.com). Development
happens inside a dev container that provisions the toolchain for you.

## Getting started

1. Open the repository in VS Code and rebuild/reopen it in the dev container when prompted. The
   container installs Deno, the GitHub CLI, and Ollama.
2. On container start, `.devcontainer/ensure-ollama.sh` runs automatically. It starts the Ollama
   server if it is not already running and pulls the cloud models this project uses:
   - `glm-5.3-flash:cloud`
   - `glm-5.3:cloud`

## Why Ollama is included

Ollama exists purely as an **optional development aid**. The
[Ollama extension for VS Code](https://marketplace.visualstudio.com/items?itemName=Ollama.ollama)
(installed by the dev container) makes Ollama models appear in the model picker of the GitHub
Copilot Chat session window, where they can be selected alongside the usual Copilot models. It is
**not a dependency of the project itself** — nothing in Lapis builds on it, the test suite does not
touch it, and you can ignore it entirely if you do not want it.

The only mandatory part of working on this project is Deno. If you would rather not use Ollama, you
can simply skip the authentication step below; the dev container will still work normally.

## Ollama authentication

The cloud models used by this project run on Ollama's servers rather than locally, so pulling them
requires an authenticated [ollama.com](https://ollama.com) account. Authentication is tied to a
private key stored at `~/.ollama/id_ed25519`, which the dev container persists across rebuilds in a
named Docker volume.

### First-time setup

The startup script creates an anonymous key automatically, but cloud model pulls fail until that key
is linked to an account. If a rebuild is your first time in the container (or the volume was created
fresh), run:

```sh
ollama signin
```

This prints a URL and a device code. Open the URL in a browser, sign in to ollama.com (creating an
account if needed), and enter the device code.

After signing in, if any models are still missing, either restart the container or pull them
manually:

```sh
ollama pull glm-5.3-flash:cloud
ollama pull glm-5.3:cloud
```

Verify everything is available:

```sh
ollama list
```

Both models should be listed. Once signed in, the key lives in the persisted volume and no further
manual steps are needed — container rebuilds will pull the models automatically.

### Troubleshooting

- **Pull failures at container start.** Check the log:
  ```sh
  cat /tmp/ollama-pull.log
  ```
  An authentication error means `ollama signin` has not been completed for the current key. Sign in,
  then pull the missing models by hand.
- **`ollama serve` fails with `permission denied` on `id_ed25519`.** The startup script repairs the
  ownership of `~/.ollama` automatically (the container has passwordless sudo). If you hit this
  outside the script, run:
  ```sh
  sudo chown -R "$(id -u):$(id -g)" ~/.ollama
  ```
- **Server does not come up.** Check the server log:
  ```sh
  cat /tmp/ollama.log
  ```

## Development

- Format: `deno fmt`
- Lint: `deno lint`
- Tests: `deno test`
