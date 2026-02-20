FROM node:20-slim

WORKDIR /app

# Install Python for running SWARM scripts
RUN apt-get update && apt-get install -y python3 python3-pip git && \
    rm -rf /var/lib/apt/lists/*

# Install Node dependencies
COPY package.json package-lock.json ./
RUN npm ci --production

# Copy source
COPY tsconfig.json ./
COPY src/ src/

# Install Python dependencies for scripts
COPY ../scripts/requirements.txt /tmp/requirements.txt
RUN pip3 install --break-system-packages -r /tmp/requirements.txt 2>/dev/null || true

ENV NODE_ENV=production
ENV PORT=3000

EXPOSE 3000

HEALTHCHECK --interval=30s --timeout=5s --retries=3 \
  CMD curl -f http://localhost:3000/health || exit 1

CMD ["npx", "tsx", "src/serve.ts"]
