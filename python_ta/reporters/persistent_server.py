"""This module defines a HTML server using aiohttp that supports reloading via WebSockets."""

import asyncio
import logging
import threading
import webbrowser

from aiohttp import WSMsgType, web

logging.getLogger("aiohttp.access").disabled = True
latest_html: bytes = b"<h1>Loading report...</h1>"
websockets = set()
server_started = False
loop = asyncio.get_event_loop()


async def handle_report(request):
    """Serve the current HTML content at the root endpoint ('/')."""
    return web.Response(body=latest_html, content_type="text/html")


async def websocket_handler(request):
    """Handle WebSocket connections, tracking clients and listening for errors."""
    ws = web.WebSocketResponse()
    await ws.prepare(request)

    websockets.add(ws)

    try:
        async for msg in ws:
            if msg.type == WSMsgType.ERROR:
                print(f"WebSocket error: {ws.exception()}")
    finally:
        websockets.remove(ws)
    return ws


async def update_report(new_html: bytes, port: int):
    """Update the served HTML content and notify connected WebSocket clients to reload."""
    global latest_html
    latest_html = new_html

    active = [ws for ws in websockets if not ws.closed]
    if active:
        for ws in active:
            await ws.send_str("reload")
    else:
        webbrowser.open(f"http://localhost:{port}", new=2)


def start_server_once(initial_html: bytes, port: int = 8000):
    """Start the HTML and WebSocket server if not already running, or update content if running."""
    global server_started
    if not server_started:
        server_started = True

        threading.Thread(target=loop.run_forever, daemon=True).start()

        asyncio.run_coroutine_threadsafe(run_server(port), loop)
        asyncio.run_coroutine_threadsafe(update_report(initial_html, port), loop)
    else:
        asyncio.run_coroutine_threadsafe(update_report(initial_html, port), loop)


async def run_server(port: int):
    """Launch the aiohttp web server on the specified port with routes for HTML and WebSocket."""
    app = web.Application()
    app.router.add_get("/", handle_report)
    app.router.add_get("/ws", websocket_handler)

    runner = web.AppRunner(app)
    await runner.setup()
    site = web.TCPSite(runner, "localhost", port)
    await site.start()
