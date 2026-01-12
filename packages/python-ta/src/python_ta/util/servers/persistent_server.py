"""This module defines a HTML server using aiohttp that supports reloading via WebSockets."""

import asyncio
import logging
import threading
import webbrowser

from aiohttp import WSMsgType, web

LOADING_HTML = b"<h1>Loading report...</h1>"


class PersistentHTMLServer:
    """A persistent HTML server that serves HTML content and supports WebSocket connections."""

    def __init__(self, port: int):
        self.port = port
        self.latest_html = LOADING_HTML
        self.websockets = set()
        self.server_started = False
        self.loop = asyncio.new_event_loop()
        asyncio.set_event_loop(self.loop)

    async def handle_report(self, request: web.Request) -> web.Response:
        """Serve the current HTML content at the root endpoint ('/')."""
        return web.Response(body=self.latest_html, content_type="text/html")

    async def handle_websocket(self, request: web.Request) -> web.WebSocketResponse:
        """Handle WebSocket connections, tracking clients and listening for errors."""
        ws = web.WebSocketResponse()
        await ws.prepare(request)

        self.websockets.add(ws)
        try:
            async for msg in ws:
                if msg.type == WSMsgType.ERROR:
                    print(f"WebSocket error: {ws.exception()}")
        finally:
            self.websockets.remove(ws)
        return ws

    async def update_report(self, new_html: bytes) -> None:
        """Update the served HTML content and notify connected WebSocket clients to reload."""
        self.latest_html = new_html

        active = [ws for ws in self.websockets if not ws.closed]
        if active:
            for ws in active:
                await ws.send_str("reload")
        else:
            webbrowser.open(f"http://localhost:{self.port}", new=2)

    def start_server_once(self, initial_html: bytes) -> None:
        """Start the HTML and WebSocket server if not already running, or update content if running."""
        logging.getLogger("aiohttp.access").disabled = True
        if not self.server_started:
            self.server_started = True
            self.loop.create_task(self.run_server())
            self.loop.create_task(self.update_report(initial_html))
            threading.Thread(target=self.loop.run_forever, daemon=True).start()
        else:
            asyncio.run_coroutine_threadsafe(self.update_report(initial_html), self.loop)

    async def run_server(self) -> None:
        """Launch the aiohttp web server on the specified port with routes for HTML and WebSocket."""
        app = web.Application()
        app.router.add_get("/", self.handle_report)
        app.router.add_get("/ws", self.handle_websocket)

        runner = web.AppRunner(app)
        await runner.setup()
        site = web.TCPSite(runner, "localhost", self.port)
        await site.start()
