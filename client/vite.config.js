import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';
var clientHost = process.env.HOST || '127.0.0.1';
var serverOrigin = process.env.SERVER_ORIGIN || 'http://127.0.0.1:5001';
var allowedHosts = ['shine.athergrid.dev', 'rmkcetshine.me'];
export default defineConfig({
    plugins: [react()],
    build: {
        rollupOptions: {
            output: {
                manualChunks: {
                    react: ['react', 'react-dom'],
                },
            },
        },
    },
    server: {
        host: clientHost,
        port: 5000,
        strictPort: true,
        allowedHosts: allowedHosts,
        proxy: {
            '/api': {
                target: serverOrigin,
                changeOrigin: true,
            },
            '/auth': {
                target: serverOrigin,
                changeOrigin: true,
            },
        },
    },
    preview: {
        host: clientHost,
        port: 5000,
        strictPort: true,
        allowedHosts: allowedHosts,
        proxy: {
            '/api': {
                target: serverOrigin,
                changeOrigin: true,
            },
            '/auth': {
                target: serverOrigin,
                changeOrigin: true,
            },
        },
    },
});
