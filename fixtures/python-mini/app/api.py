from services.worker import start

def create_app():
    start()
    return {"ok": True}
